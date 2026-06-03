# Macro-availability model — the foundation under W-Macro (S76)

**Status — DECISION LOCKED (user-approved 2026-06-03).** The macro-availability foundation is settled. This document is now in two layers:

- **§0 (LOCKED decision)** — the normative model. Read this first; it is the working reference.
- **§1–§7 (deep-dive trace, SUPERSEDED as recommendation)** — the S76 Phase 3 design-space exploration that *drove* the locked decision. Its option-space analysis (§2), Option-(f) recommendation (§4–§7), and especially the **§4.4 concrete trace** are retained as the **disproof record** — they are *why* the simpler "expand-before-check_forms over a best-effort use-before-def model" collapsed and the locked decision took its present shape. The recommendation layer (Option (f), the (f)-vs-(a) framing, the §4.3 "atomic-commit over the fully-expanded set as target" hedging) is **SUPERSEDED by §0**. Where §0 and §1–§7 conflict, §0 governs. Each superseded section carries an inline pointer to §0; nothing is deleted (the trace is the legible record of what was ruled out and why).

This is a cross-crate + cross-spec foundation, so it lives in `design/arch/`. The locked rule cascades into: the spec (via FIXMEs 0005/0006/0007 — `/spec`-owned), `bounded-contexts.md` §1 (frontend — quasiquote-only), §2 (typecheck — recognition role + three-pass), §6 (int — orchestrates Pass 1 + supplies `MacroExpander`), `exec-flow-compilation.mmd`+`.svg` (three-pass), `macro-expansion-ownership.md` (the mechanism doc this grounds, §4.3 pinned to the three-pass). No new Decision file (manifestation-site discipline — the commitment lives in the BC sections, these design docs, and the FIXME spec-text).

---

## 0. THE LOCKED DECISION (user-approved 2026-06-03)

After an extended source-grounded pressure-test (the trace in §4.4 below disproved the as-built handling and refuted two intermediate models — see §0.5), the user settled the macro-availability foundation. This section is normative; §1–§7 are the exploration that produced it.

### 0.1 The principle (user-visible, in typecheck/dependency terms)

A macro's **expansion** may reference only:

1. **Modules typechecked before its defining module** — i.e. the defining module's **dependencies**. The compiler realizes this by *pausing* the current module's typecheck to typecheck-and-compile a dependency **just-in-time** when the expansion first needs it, then resuming. (This is the same pause-and-fetch mechanism the scheduler already runs for cross-module value/type references — Decision 0030 — applied to the macro compile-time layer.)
2. **Macros** — including **same-module macros**. Macros are the compile-time layer; by construction they are dependent only on prior modules (principle 1 applied recursively), so a macro is always safe to reference at expansion time.

A **same-module non-macro definition is NOT available at expansion time.** A `defmacro` clause body MUST NOT call a same-module `defn` helper (nor read a same-module `def`/`const` value) at expansion time. If the clause needs a helper, that helper lives in a **dependency module** (which is typechecked-and-compiled before the defining module, hence available), or the logic is inlined into the clause body.

**Dependencies cannot refer back** — the module dependency graph is **acyclic**. A dependency typechecked before module M cannot, in turn, depend on M.

### 0.2 defmacro-before-use is NORMATIVE

Within a module, a macro MUST be **defined before it is used**, in source order. A use that appears textually *before* its `defmacro` is **not** a macro call — it is a plain unresolved reference (it passes through to the AST builder as an ordinary function reference and fails name resolution there if undefined). This is a normative spec rule (goes into §9.3.4 + §5.13.2 — see §0.6).

This **retires** the prior "module-wide macro availability / use-before-def" claim and the deep-dive's Option-(f) "best-effort use-before-def within a cluster" — both are superseded. The rule is the simple, predictable one: define the macro before you use it.

### 0.3 The deciding constraint — round-trip safety (REPL ≡ batch by construction)

The reason a same-module non-macro definition is forbidden at expansion is **round-trip safety**, not a Clojure-parity calculation:

`regenerate_backing_file` writes the live session back to disk as **one batch module**. Anything a macro touches *at expansion time* must therefore be in a **dependency** — because when the regenerated single-module file is recompiled, a same-module helper is a Pass-2/3 entity (see §0.4) that does not exist yet when the macro expands. If macros were permitted to call same-module helpers at expansion, the regenerated file would **fail to recompile** — the round-trip would not be safe. Forbidding same-module non-macro expansion-time references makes **REPL ≡ batch by construction**: whatever expands in the REPL also expands identically in the regenerated batch file, because both resolve expansion-time references against dependencies only.

This is the constraint the deep dive's §4.4 trace exposed (a same-module `defn` helper's *code* is absent when the clause executes) and the user's round-trip-safety framing turned into the governing principle.

### 0.4 Three-pass module compilation (the implementation shape)

A module compiles in three passes:

1. **Pass 1 — Recursively typecheck defmacros and expand all macro symbols** (both local and FQ), compiling dependent forms just-in-time as needed. This is the **compile-time layer**.
   - *"Recursively"* = a macro-generated `defmacro` is itself typechecked/compiled and becomes available to subsequent expansion in the same pass; the expansion runs to fixpoint.
   - *FQ `mod/macro` references* trigger just-in-time typecheck/compile of the referenced module (FIXME 0007's FQ-macro-ref capability, **folded into Pass 1** — it is not a separate mechanism).
   - Dependency forms a macro clause needs are JIT-compiled on demand via the pause-and-typecheck (just-in-time) mechanism.
2. **Pass 2 — Scan non-macro signatures** (cluster-wide, over the fully-expanded form set, including macro-generated definitions).
3. **Pass 3 — Typecheck non-macro bodies** (cluster-atomic, against the complete registered signature/impl set).

**Key structural property — the pass order ENFORCES the stage restriction.** Pass-1 expansion runs *before* Passes 2–3, so when a macro clause executes the module's own non-macro definitions have **not yet been processed** (they are Pass-2/3 entities) and are therefore **structurally invisible** at expansion. The §0.1 restriction ("no same-module non-macro definition at expansion") is a **consequence of pass ordering, not a separate check** — there is nothing to enforce dynamically because the non-macro entries do not exist when Pass 1 runs.

### 0.5 Decision 44 reconciliation — intact

Decision 44's cluster-atomicity is **intact** and now operates cleanly on the **Pass-2/3 runtime layer** (the fully-expanded non-macro forms):

- `check_forms`'s internal two passes **ARE Passes 2 + 3** (Pass 2 = signature registration into staging; Pass 3 = body typecheck against the unioned staging+live view; atomic commit on whole-cluster `Ok`).
- The **compile-time layer (Pass 1)** runs *before* `check_forms`, orchestrated by int's `process_cluster` expand loop, and is resolved against **dependencies only**. Pass 1 is **self-sufficient** precisely because expansion helpers are dependencies (typechecked-before), not same-module entities.
- `check_forms` therefore receives an **already-fully-expanded** `Vec<ParsedEntry>` and never triggers macro execution. D44's atomic-commit property is over that expanded entry set, **unchanged** — and this is now a true statement of the design (not the "target, not as-built" hedge the §4.3 caveat carried for Option (f)), because the locked decision removes the same-module mid-cluster clause-commit hazard the trace found: there is no same-module-helper compile interleaved with the cluster check.

This **vindicates the deep dive's "expand before check_forms" shape** (§4.3 / `macro-expansion-ownership.md` §4.3 "second/cleaner shape") — and it is sound *because* Pass-1 expansion helpers are **dependencies**, not same-module helpers. The earlier disproof (§4.4) applied only to **same-module** helpers, which the locked principle now **forbids**. Removing that case removes the unsoundness.

### 0.6 What lands in the spec (routed to /spec via FIXMEs 0005/0006/0007 — see §5, rewritten)

- **§9.3.4 + §5.13.2** — defmacro-before-use is normative; "expansion references dependencies (typechecked-before) + macros, not same-module non-macro definitions"; REPL ≡ batch unification (a file is one cluster; the macro-availability rule is the same in REPL and batch by construction of the round-trip-safety constraint). Strike the "extracts and compiles all defmacro in a pre-pass" / "MAY be used before its defmacro" claims and the §5.13.2 internal contradiction.
- **§9.8 / §9.12** — the three-pass model (recursively-typecheck-defmacros-and-expand-all → scan-non-macro-sigs → typecheck-non-macro-bodies). **Drop** the "macro bodies can call helper functions defined earlier in the file" claim; **replace** it with the dependency rule (macro bodies may call helpers defined in **dependency modules**, and same-module **macros**, not same-module non-macro definitions).
- **§8.5.1 + new §9.3.6** — FQ macro references authorized (now folded into Pass 1).

### 0.7 W-Macro mechanism (pinned — supersedes the provisional shapes)

- **Pass 1 = the expand phase**, orchestrated by int's `process_cluster`. Macro heads are recognized via the **`cranelisp-types` resolution primitive** `cranelisp_types::resolve_macro_head` (module-local per Principle 17), which int calls directly over the **committed** symbol tables (`View::single(live)` first-hop — no staging exists during Pass 1). Recognition is therefore a types query with **zero int→typecheck dependency** (resolution-primitive fold-in, 2026-06-03). int's `cranelisp_types::MacroExpander` callback (impl over `src/expander.rs`'s invocation core + `src/marshal.rs`) executes the compiled clause; dependency forms are JIT-compiled on demand via the pause-and-typecheck mechanism. The expansion runs to fixpoint (nested macros + structural re-classification — `def` → `(begin (defn …) (defmacro …))` — re-enter the expand loop). The fully-expanded `Vec<ParsedEntry>` then feeds one `check_forms` call.
- **Passes 2 + 3 = `check_forms`** (its internal two-pass discipline over the fully-expanded non-macro forms). Typecheck's body-resolution `resolve_*` family are thin callers of the same `cranelisp_types::resolve` primitive, supplying the staging ∪ live first-hop view.
- **No public-API delta on the typecheck/int boundary** beyond the already-authored `MacroExpander` trait + `MacroInvokeError` enum (`crates/cranelisp-types/src/macro_expander.rs`). The resolution-primitive fold-in adds a **`cranelisp-types` surface** (`resolve` / `resolve_macro_head` / `Resolved` / `ResolveError`; +~40 lines to `crates/cranelisp-types/public-api.txt`) and **removes** the recognition logic from typecheck's surface entirely (recognition is now a types query, not a typecheck-exposed predicate — superseding the prior FIXME-0245 "typecheck-interior recognition surface" framing). The locked decision settles *semantics* + *sequencing*; the fold-in settles the *placement of resolution* (types-owned primitive + caller-chosen view). No new typecheck/int boundary type. See `bounded-contexts.md` §7 "Resolution primitive" + `interfaces.md`.

**The §4.4 trace's "net-new int-side step" (codegen a macro clause's transitive `defn`-callee closure before invoking) is RESOLVED by the locked decision, not carried forward.** Under Option (f), that step was needed because a clause could call a same-module `defn`. The locked decision **forbids** same-module non-macro expansion-time references — so the clause's callees are **dependency** functions (already compiled, by Pass-1's just-in-time dependency compilation) or same-module **macros** (compiled in Pass 1). There is no same-module-`defn`-callee-with-empty-GOT-slot case to wire `block_for_macro_codegen` for. The dead `block_for_macro_codegen` path can be deleted rather than wired live. (`/dev` (int) confirms the deletion when it lands the Pass-1 dependency-compile orchestration. The `facades/int.md` "Gap design rationale" cascade flagged in §4.4 — the "macro-clause callees ARE boosted" exception — is **withdrawn**: there are no same-module clause callees to boost; the rationale's "functions are NOT speculatively JIT-pushed" statement stands unqualified, because the dependency functions a clause needs are pulled in by Pass-1 just-in-time dependency compilation, not by a speculative function-caller boost.)

### 0.8 The defect repro still belongs in the suite

The `stdlib/defs.cl:20-22` workaround and the `helper → m → f` scenario remain a useful regression guard — but their **disposition flips**: under the locked decision the `helper → m → f` (same-module `defn` helper called by a macro clause) shape is **not** a defect-to-fix — it is a **rejected program** (defmacro-clause calls same-module non-macro `defn` → not allowed; the helper must move to a dependency module). `/qa`'s narrow test should assert that this shape produces a **clear diagnostic** ("macro expansion may not reference same-module non-macro definition `helper`; define it in a dependency module"), NOT that it expands successfully. The `stdlib/defs.cl` inline-the-mangling workaround is, under the locked decision, the **correct** authoring pattern (a macro inlines its logic rather than calling a same-module helper) — not a workaround for a bug. `/sprint` routes this test framing to `/qa` alongside the spec change.

### 0.9 Resolution-primitive placement (folded in 2026-06-03, user-approved)

A refinement folded in on top of the locked decision (it does NOT touch the §0.1–§0.6 macro-availability semantics — it settles *where the name-resolution mechanism lives*, an implementation-internal, language-invisible placement):

- **The symbol-table resolution/search primitive is types-owned.** Resolving a name (from a current module, following imports/reexports/aliases, visibility, and Principle-17 chain-following) is a **query over the symbol-table data structure** — no inference, no unification, no substitution. By Principle 15 (behaviour lives with the type) and Principle 7 (single source) it lives on `SymbolTables` in `cranelisp-types`, extending the `ensure_module_exists` + `got_data_symbol_name` precedent. Authored as `cranelisp_types::resolve` (general primitive) + `cranelisp_types::resolve_macro_head` (the macro-recognition wrapper) + `Resolved` + `ResolveError` (relocated from typecheck). Pure over `symbol_tables` + `module_aliases`, generic `<C, L>`, **no `CheckState`**.
- **The choice of which view to search stays with the caller.** int's Pass-1 macro recognition searches the **committed** tables (`View::single(live)` first-hop); typecheck's Pass-2/3 body resolution searches the **staging ∪ live union** (`View::union` via its `SymbolTableAccess`). Same primitive, different first-hop view.
- **Effect.** Macro recognition leaves typecheck's surface entirely (it is a `cranelisp-types` query); int does Pass-1 recognition with **zero int→typecheck dependency for recognition**; int's former `SymbolTableMacroResolver` (`src/worker.rs`) AND typecheck's `resolve_trait`/`resolve_type`/`resolve_constructor`/`resolve_qualified` family (S72) **both consolidate onto the types primitive** (retiring two scattered copies). **No DAG impact** (types has no deps). Public-API delta: +~40 lines on `crates/cranelisp-types/public-api.txt` (the `resolve`/`resolve_macro_head`/`Resolved`/`ResolveError` surface). Manifestation sites: `bounded-contexts.md` §7 ("Resolution primitive") + §2 (typecheck caller) + §6 (int Pass-1), `interfaces.md` ("Resolution primitive"), and the `crates/cranelisp-types/src/resolve.rs` rustdoc. The caller-side wiring (typecheck's `resolve_*` re-pointed at the primitive; int's recognition call) is pinned by `/design (typecheck)` + `/dev` in the Phase-3/implementation waves.

---

## 1. The problem, stated precisely

A `defmacro` is **executable code**. To expand a macro call `(m args)`, the compiler must (in order):

1. **Recognize** `m`'s head as a macro (not a fn) — a symbol-table lookup that needs `m`'s *signature* registered.
2. **Have `m`'s clause code in memory** — the JIT'd clause body, reachable by GOT address.
3. **Execute** the clause: marshal `args` Sexp→heap, call the clause under signal protection, marshal the result heap→Sexp.
4. **Re-process** the result: it may contain further macro calls (nested fixpoint) and may be a *structural* shape (`def` → `(begin (defn …) (defmacro …))`) that re-enters form-classification.

The dependency chain that makes this **fundamentally sequential**:

> a `defmacro`'s body may itself call earlier macros → so the defmacro must be **expanded** (step 1–4 on its own body) → then **built** (AST) → then **typechecked** → then **JIT-codegened** → only *then* is its clause code in memory (step 2 satisfied) → only then can a **sibling form that calls it** be expanded.

This collides with two architectural commitments and one spec inconsistency:

### 1.1 Collision A — the form-by-form streaming pillar

v4 is form-by-form streaming (overview.md; the pipeline pillar). The scheduler processes forms; a `defmacro` becomes *executable* only after its form is typechecked + JIT-codegened. There is no global "compile all macros first" phase in the streaming model — that would be a pre-pass, which the pillar rejects.

### 1.2 Collision B — Decision 44 cluster-atomicity

Decision 44: `check_forms` iterates **all** cluster forms — Pass 1 registers every signature into staging, Pass 2 checks every body — then commits atomically. A batch file is "one big cluster" (`src/CLAUDE.md`). But macro expansion of form *N* needs macro *M* (defined at form *K < N* in the same cluster) **already JIT-codegened** — and JIT-codegen happens *after* typecheck commit, *outside* `check_forms`. So expansion-needs-codegen is a mid-cluster sequencing dependency that Decision 44's "all-signatures-then-all-bodies over one atomic frame" does not, by itself, express.

### 1.3 The spec is self-inconsistent (FIXMEs 0005/0006/0007)

- **§9.8 / §9.3.4 (REPL) + §5.13.2 (REPL clusters)** mandate **use-after-definition**: "a macro MUST be defined (or appear earlier in the same `begin` cluster) before its first use" (§5.13.2 line 623); REPL forms are source-order, one-per-eval.
- **§9.3.4 (batch) + §5.13.2 batch paragraph (line 629) + §9.12 (bootstrapping)** claim a **pre-pass**: "all `defmacro` forms are extracted and compiled in a pre-pass before other forms are processed… a macro MAY be used before its `defmacro` form in source order, consistent with Clojure's module-wide macro model." The §5.13.2 batch example (lines 631-638) shows `(defn f [x] (double x))` *before* `(defmacro double …)`.

§5.13.2 is **internally contradictory**: line 610-621 state REPL has no forward references and the file scope is "effectively one cluster" with §5.13.1 two-pass semantics; line 629 then claims macros specifically get a *separate* pre-pass with use-before-def. The two cannot both hold for a file-as-one-cluster model.

### 1.4 What the source actually does today (the feasibility evidence)

`src/worker.rs::process_module_forms` (the real current batch path):

- **Pass 0** — structural decls (import/export/mod/platform) recorded.
- **Pass 1** — `separate_macros(sexps)` extracts **all** `defmacro` forms from the module up front and registers **every macro signature** into the symbol table (`register_macro_in_module`), alongside all regular-form signatures (`pass1_register`). So macro **recognition** is module-wide as of Pass 1 — a head is recognizable as a macro even before its defmacro in source order.
- **Pass 2** — per-form expand-then-check, source-order. Each `defmacro` is JIT-compiled (`compile_macro_if_needed`) **when Pass 2 reaches it**. Regular forms are expanded (`try_expand_sexp`); a macro call expands only if the macro's clause code is already in memory.

**The crucial split the source already embodies:** *recognition* is module-wide (Pass 1 signature pre-pass), but *execution* is source-order (Pass 2 JITs each defmacro at its position). A forward macro use — `f` calling `double` before `double`'s defmacro — would be **recognized** as a macro head, but `double`'s clause code is not yet in memory when `f` is expanded. Today this is handled (where it works) by the gap/priority-boost mechanism the provisional `exec-flow-compilation.mmd` depicts (`MacroInMem` gap → `priority_boost_jit` + `wait_for_inmem`). It is NOT a separate "compile all macro bodies first" pre-pass — only the *signatures* are pre-passed.

> **This is the key insight the prior W-Macro pass missed.** "Macro availability" is not one decision. It is two: **recognition availability** (when is a head known to be a macro?) and **execution availability** (when is the clause code runnable?). They are settled by different mechanisms (signature registration vs JIT-codegen ordering) and admit different answers. The spec inconsistency is precisely the result of conflating them — §9.3.4's "pre-pass" speaks of *compilation* (execution) but is satisfiable, in part, by a *signature* pre-pass (recognition). Separating the two dissolves most of the tension.

---

## 2. The option space

> **SUPERSEDED by §0 (2026-06-03 lock).** The option space below (a)–(f) explored *whether* same-module use-before-def is supported and *how* a clause's same-module callees are compiled. The locked decision (§0) cut beneath this axis: same-module non-macro definitions are **forbidden** at expansion time (round-trip safety, §0.3), and **defmacro-before-use is normative** (§0.2). Under §0 the relevant axis is no longer (a)-vs-(f) recognition rules but the **three-pass phase-by-dependency** model (§0.4). Retained as the exploration that drove the lock — especially the §4.4 trace, which is the disproof that collapsed the best-effort-use-before-def family.

Each option is scored on: **within-cluster sequencing** (how does form *N* get macro *M*'s code?); **D44 reconciliation**; **form-by-form fit**; **language semantics** (use-before-def? REPL/batch parity? Clojure divergence?); and the **resulting W-Macro mechanism**.

### Option (a) — Pure form-by-form, use-after-definition only

Drop the pre-pass claim entirely. A macro is available (recognizable AND executable) only to forms that **follow** its defmacro in source order, in both batch and REPL.

- **Sequencing:** trivial — `M` is fully processed (expanded/built/checked/JIT'd) before any form after it; form *N>K* finds `M`'s code in memory. No gap needed for in-module macros (cross-module FQ macros still gap, per §3).
- **D44:** intact, but the file-as-one-cluster model must yield: a `defmacro` cannot be JIT-codegened *inside* `check_forms` (codegen is post-commit). So either (a1) each top-level form is its own cluster (loses §5.13.1 forward refs for fns/types — a regression), or (a2) defmacro forces a cluster boundary (= option (e); the in-module-streaming-with-boundaries hybrid). Pure (a) at file scope without sub-clustering is incompatible with "file = one big cluster" because the cluster cannot both atomically-commit-all-bodies AND interleave per-defmacro codegen. **So (a) only stands at file scope via (e).**
- **Form-by-form fit:** perfect.
- **Semantics:** no use-before-def, **anywhere**. REPL/batch fully unified (the simplest possible story). Clojure divergence: Clojure macros are module-wide (use-before-def works); Cranelisp would not match. FIXME 0005 calls this divergence "intentional."
- **Mechanism:** typecheck recognizes (signature in staging/live for forms ≤ current); int executes via callback; no `MacroInMem` gap for in-module macros (code always already present). Simplest mechanism.

### Option (b) — Pre-pass per module (hybrid: pre-pass within module, streaming across)

Eagerly scan + **fully compile** (expand/build/check/JIT) all `defmacro`s in a module before processing any other form; other forms stream form-by-form.

- **Sequencing:** all macro code in memory before any regular form — no gap, use-before-def works.
- **D44:** macro compilation is a *separate phase* before the regular-form cluster; the regular-form cluster is then D44-atomic over non-macro forms. Macros are NOT in the atomic cluster — a mid-cluster failure does not roll back already-committed macros. This **scopes** D44 (atomicity covers the regular-form cluster, not the macro pre-pass) and reintroduces a phase the form-by-form pillar rejects.
- **Form-by-form fit:** poor — reinstates a pre-pass (FIXME 0005 option (b); `/arch` already rejected on pillar grounds).
- **Semantics:** use-before-def for macros within a module; matches Clojure; REPL still use-after (REPL has no module pre-pass) → **batch/REPL divergence persists** (the status-quo split).
- **Mechanism:** a macro sub-phase in `process_module_forms` before the cluster; recognition + execution both satisfied up front; no in-module gap. More machinery; defies the pillar.

### Option (c) — Defmacro signature in the structural pre-scan (recognition pre-pass only)

Treat `defmacro` *signature registration* as part of the existing structural pre-scan (`separate_macros` today already does this in Pass 1) — so macro **recognition** is module-wide — but leave macro **execution** (JIT-codegen) in the source-order stream. This is **what the source does today.**

- **Sequencing:** recognition is module-wide; execution is source-order. A forward macro use is recognized but its code may not be in memory → resolved by the `MacroInMem` gap + `priority_boost_jit` (compile that one macro on demand, ahead of stream position).
- **D44:** the regular-form cluster stays atomic; macro *signatures* register in Pass 1 of the same cluster (no separate phase for recognition). Macro *codegen* is post-commit (as today). The gap mechanism handles the "need M's code now" case by boosting M's compilation. D44 is **intact** for the atomic-commit property; the gap is an orthogonal scheduler concern (it predates W-Macro — it is the same mechanism used for cross-module value/type refs).
- **Form-by-form fit:** good — no global pre-pass; only signature registration is module-scoped (and signature registration is already module-scoped for *every* definition in a cluster under D44's Pass 1). The "pre-pass" is not special to macros; it is Pass 1.
- **Semantics:** use-before-def **works** for in-module macros (recognized + gap-compiled on demand), matching Clojure — IF the gap mechanism can compile a forward macro whose own body has no unsatisfiable forward dependency. REPL: a single REPL input is a one-form cluster (no forward refs); `(begin …)` is a multi-form cluster where Pass 1 registers all macro signatures → in-cluster forward macro use works. **This achieves batch/REPL parity at the cluster granularity** (file = one cluster → module-wide; REPL form = one cluster → no forward; REPL `begin` = one cluster → forward within).
- **Mechanism:** exactly the provisional `exec-flow-compilation.mmd` shape — typecheck recognizes (Pass-1 signatures make every macro head recognizable cluster-wide), surfaces `MacroInMem` for not-yet-JIT'd macros, int boosts + executes via callback. **This is the current as-built mechanism, made principled.**

### Option (d) — Defmacro as a scheduler dependency node (on-demand via gap)

Macros form their own dependency sub-graph; a macro is compiled on-demand the first time a sibling needs to expand a call to it, via the existing `Gap(MacroInMem)` + `priority_boost_jit`.

- **Sequencing:** lazy — `M` compiles when first needed. Forward use triggers the gap.
- **D44:** as (c) for the recognition side (signatures must still be registered for the gap to know the head is a macro). Differs from (c) only in *whether macro signatures are pre-registered cluster-wide* (c: yes, in Pass 1) *or discovered lazily* (d: the head is unknown until M's defmacro is reached). Pure (d) without (c)'s signature pre-pass means a forward macro head is NOT recognized as a macro (it looks like an unknown fn) — so pure (d) gives **use-after-def** (same observable semantics as (a)), with a lazy-compile mechanism that buys nothing for in-module macros (they're source-order anyway) and matters only for cross-module FQ macros.
- **Form-by-form fit:** good.
- **Semantics:** without (c), use-after-def only. With (c) layered on, it *is* (c).
- **Mechanism:** the gap is real and needed — but for **cross-module FQ macro references** (§3), not for in-module forward refs. (d) is best understood as "the cross-module half of the mechanism," complementary to whichever in-module recognition rule (a/c) is chosen.

### Option (e) — Defmacro forces a cluster/sub-cluster boundary

A file becomes a **sequence of clusters split at each `defmacro`**. Each defmacro is its own (one-form) cluster, compiled+JIT'd, before the next cluster of regular forms. Reconciles D44 by **shrinking the atomic unit**.

- **Sequencing:** each defmacro's code is in memory before the next cluster's forms are expanded — clean, no gap for in-module macros.
- **D44:** **amends** D44 — "file = one big cluster" becomes "file = a sequence of clusters, boundaries at defmacro forms." Atomicity is per-sub-cluster, not per-file. This breaks **fn/type forward references across a defmacro boundary**: `(defn even? …)` … `(defmacro m …)` … `(defn odd? …)` would put `even?` and `odd?` in different clusters → mutual recursion across the defmacro fails (a §5.13.1 regression).
- **Form-by-form fit:** good (it IS streaming, at cluster granularity).
- **Semantics:** use-after-def for macros (a macro is in an earlier cluster than its users); but fn/type forward-reference scope shrinks (regression vs §5.13.1). REPL parity awkward (REPL is already per-cluster).
- **Mechanism:** no in-module gap; orchestrator splits the form stream at defmacro. Conceptually clean but pays a real §5.13.1 forward-reference tax.

### Option (f) — Hybrid: (c) recognition pre-pass + (d) cross-module gap (RECOMMENDED)

Layer (c) and (d) deliberately, recognizing they answer different questions:

- **Recognition** (in-module): macro signatures register cluster-wide in Pass 1 (= (c) = the existing `separate_macros` behavior, reframed as "Pass 1 registers all signatures, macros included"). Every in-module macro head is recognizable cluster-wide.
- **Execution** (in-module forward use): the `MacroInMem` gap (= (d)) compiles a not-yet-JIT'd in-module macro on demand when a preceding form expands a call to it. This gives **use-before-def within a cluster** without a separate macro pre-pass and without a global codegen phase.
- **Cross-module**: FQ macro references (`mod/macro`) trigger lazy module registration + typecheck + `wait_for_inmem` (FIXME 0007) — the same gap mechanism, applied across modules. Not source-order constrained.

This is the option that **matches what the source already does**, **honours the form-by-form pillar** (no pre-pass beyond Pass-1 signatures, which D44 already mandates for *all* definitions), **keeps D44 intact** (atomic-commit unchanged; the gap is orthogonal), and **delivers the provisional mechanism** in `macro-expansion-ownership.md` + `exec-flow-compilation.mmd` without change.

---

## 3. Option-space summary table

| Option | In-cluster sequencing | D44 | Form-by-form | Use-before-def | REPL/batch parity | Mechanism cost |
|---|---|---|---|---|---|---|
| (a) pure form-by-form | trivial (M before N) | needs (e) at file scope | perfect | NO (anywhere) | full parity (simplest) | minimal; no in-module gap |
| (b) module pre-pass | all-macros-first | scopes D44 (macros outside atomic cluster) | poor (pre-pass) | YES (batch only) | divergent (REPL use-after) | macro sub-phase; defies pillar |
| (c) recognition pre-pass | recognize cluster-wide; gap for code | intact | good | YES (via gap) | parity at cluster granularity | = current source |
| (d) scheduler dep node | lazy compile on demand | intact (recognition needs (c)) | good | only with (c) | as (a) without (c) | gap; redundant in-module without (c) |
| (e) defmacro = cluster boundary | M's cluster before N's | **amends** D44 (sub-clusters) | good | NO (macros earlier cluster) | awkward | split stream; §5.13.1 tax |
| **(f) (c)+(d) hybrid** | **recognize cluster-wide (Pass 1); gap compiles forward/cross-mod** | **intact** | **good** | **YES (in-cluster + cross-module)** | **parity at cluster granularity** | **= provisional mechanism; reuses existing gap** |

---

## 4. Recommendation — Option (f)

> **SUPERSEDED by §0 (2026-06-03 lock).** Option (f) is **not** the locked outcome. The user's pressure-test (continuing past this recommendation — see §0.5 + SPRINT.md log 2026-06-03) drove the design *past* Option (f) entirely to the **three-pass phase-by-dependency** model (§0). Two refutations established along the way, both fatal to the Option-(f) family: **(i)** the §4.4 trace proved a macro clause cannot call a same-module `defn` helper as-built (empty GOT slot); **(ii)** *permitting* same-module expansion helpers (the fix Option (f) implied) **breaks `regenerate_backing_file` round-trip** — a regenerated single-module file can't use same-file helpers at expansion (§0.3). The clean resolution forbids same-module non-macro expansion references outright. §4.1–§4.3 below are retained as the grounding-in-principles narrative (most of which carries forward — form-by-form, minimum mechanism, module-locality, D44-intact — re-expressed in §0.5/§0.7); §4.4 is retained as the **disproof record**.

**Recommended way forward: Option (f) — recognition pre-pass (= D44 Pass 1) + execution-on-demand via the existing `MacroInMem` gap, applied uniformly to in-module forward use and cross-module FQ references.**

### 4.1 Why (f), grounded in the principles

- **Form-by-form pillar (overview.md).** (f) introduces **no pre-pass beyond Pass 1 signature registration** — and Pass 1 is not macro-specific: D44 already registers *every* definition's signature in Pass 1 before any body is checked. Recognizing macro heads cluster-wide is the same act, applied to the same Pass-1 sweep. The streaming model is preserved: execution (JIT-codegen) stays in the form stream; the gap handles the rare forward-execution need.

- **Principle 6 (complexity budget — minimum mechanism).** (f) is the *least* new machinery: it reuses the gap mechanism that already exists for cross-module value/type references (Decision 0030's scheduler is built around exactly this). No macro sub-phase (b), no stream-splitting (e), no §5.13.1 regression. It is, modulo the W-Macro ownership move (recognition → typecheck), **the current as-built behavior made principled** — *for the macro-recognition half*. **CORRECTION (§4.4):** the "= current as-built behaviour" claim is overstated for the macro-clause *execution* half. The macro-clause-calls-a-`defn`-helper case is **not** as-built: the source codegen's the clause but not its `defn` callees (empty-slot crash at expansion; `stdlib/defs.cl:20-22` workaround). (f) thus carries one net-new step — on-demand codegen of a clause's transitive `defn`-callee closure before invocation — which is *minimum* (reuses `inline_jit_codegen_for_names` + the already-computed `collect_transitive_uncompiled_deps` closure; wires the dead `block_for_macro_codegen` intent) but is **not** a no-op rename of an existing mechanism. The only deletion is the unprincipled bare-name "probe every module" loop (`lookup_macro_fq`), replaced by current-module-view lookup — a Principle 17 *improvement*.

- **Principle 7 (single source of truth).** Recognition reads the same symbol-table view every other head lookup uses (Pass-1-staged signatures). There is no parallel "macro environment" store — macros are `DefKind::Macro` entries in the one symbol table (matches the S70 `ModuleEntry` collapse).

- **Principle 17 (module-locality).** In-module recognition is shape-1 (unqualified short-name → current-module view → one Import hop). Cross-module FQ macro recognition is shape-2 (qualified lookup). No module-set iteration. The gap's `ensure_registered`/`wait_for_typecheck`/`priority_boost_jit` are the orchestrator's job (int), not inside `check_forms`.

- **Decision 44 (cluster-atomic).** **Intact, with one clarifying invariant** (§4.3). The atomic-commit property is untouched: a cluster's signatures (macros included) stage in Pass 1; bodies check in Pass 2; commit is all-or-nothing. The macro *codegen* that the gap triggers happens against **already-committed** macro definitions from *earlier* in the stream (or earlier clusters), or — for a true in-cluster forward macro — see §4.3.

- **Decision 0030 (scheduler).** The `MacroInMem` gap is the same priority-boost-and-wait the scheduler already runs for cross-module dependencies. (f) does not add a scheduling concept; it names an existing one for the macro case.

### 4.2 The honest cost

(f) preserves **use-before-def within a cluster** (the Clojure-like convenience) — but only where the forward macro's own body has no *unsatisfiable* dependency at the moment the gap fires. The realistic limit: a forward macro `M` used by an earlier form `N`, where `M`'s body calls another macro `P` defined *after* `M` — the gap to compile `M` would itself need to expand `M`'s body, gapping on `P`, and so on. This is bounded by the same `EXPANSION_DEPTH_LIMIT` and terminates, but a genuinely cyclic macro-uses-macro forward chain is rejected (consistent with Decision 0030's mutual-import deadlock disposition — Principle 6: the workaround is "define macros before the macros/forms that use them," which is the common case). **Naming this honestly:** (f) offers use-before-def as a *best-effort within-cluster convenience*, not a *guarantee*. The guaranteed, always-works subset is use-after-definition. If the user wants a hard guarantee with zero forward-chain surprises, that is option (a) (use-after-def only, everywhere) — strictly simpler, at the cost of the Clojure-parity convenience.

**The recommendation surfaces this as a user decision (§7).** `/arch`'s default lean is (f) because it matches the source, the provisional mechanism, and the spec's stated Clojure-parity intent — but (a) is a legitimate simplification the user may prefer for predictability.

> **COST CORRECTION (S76 W-Macro concrete trace, §4.4).** The cost stated above (the *macro-uses-macro* forward chain) is **incomplete**. The §4.4 concrete trace disproved a more basic case: a macro whose clause body calls a plain `defn` helper at expansion time. The source as-built does **not** compile the clause's `defn` callees before executing the clause — it codegen's only the clause, leaving the callee's GOT slot empty → an empty-slot indirect call at expansion time (confirmed by the `stdlib/defs.cl:20-22` workaround). **(f) therefore requires a net-new step**: on-demand codegen of a macro clause's transitive `defn`-callee closure before the clause is invoked (wiring the currently-dead `block_for_macro_codegen` path, or equivalent, over the `collect_transitive_uncompiled_deps` closure the source already computes). This is **not** "naming an existing mechanism" — it is new int-side orchestration. Crucially, **Option (a) does NOT escape this**: under (a) the helper still precedes the macro in source order, yet its *code* is still absent when the clause executes (regular-defn codegen is deferred past Pass 2). So the defect is **orthogonal to the recognition rule** — both (a) and (f) need the same function-callee-codegen addition. (a) remains simpler only for *recognition*, not for this *execution* path.

### 4.3 Decision 44 reconciliation — the clarifying invariant (manifestation site: BC §2 + Decision 0044 site)

> **SUPERSEDED/UPGRADED by §0.5 (2026-06-03 lock).** The "expand fully → then one `check_forms` over the fully-expanded set" shape below is **correct and now the locked design** — but the AS-BUILT CAVEAT hedge ("target, not as-built; D44 already scoped today") is resolved by the lock, not carried forward. Under §0 the atomic-commit-over-the-expanded-set statement is **true of the design**, full stop, because the locked decision **removes** the same-module clause-commit-to-live-mid-cluster hazard the trace found (clause callees are dependency forms compiled by Pass-1 just-in-time, outside the cluster). The compile-time layer is **Pass 1** (§0.4); `check_forms`'s two internal passes are **Passes 2+3** over the fully-expanded non-macro forms. §0.5 is the canonical reconciliation; the invariant text below is the (correct) shape it formalizes.

> **AS-BUILT CAVEAT (§4.4).** The invariant below states the **target** shape (expand fully → then one `check_forms` over the fully-expanded set). The §4.4 concrete trace found the *current source* does NOT yet honour it: macro-clause typecheck+codegen commits to **live mid-Pass-2** (before the cluster's atomic check), so D44 atomic-commit is **already scoped, not intact, today**. The invariant is what /dev must build to; "the atomic-commit property is over that expanded set, unchanged" is true of the target, not the present source. Read the assertions below as target-stating.

The one thing D44 does not *currently* state, which (f) requires, is **where in the cluster lifecycle macro execution happens relative to Pass 1 / Pass 2 / codegen.** The reconciliation is a clarifying invariant, NOT an amendment to the atomic-commit semantics:

> **Macro-expansion precedes the two-pass check.** Within a cluster, macro expansion to fixpoint runs as the orchestrator (`process_cluster`) accumulates `Vec<ParsedEntry>` — i.e., in the **build/expand loop that feeds `check_forms`**, before Pass 1 runs over the fully-expanded entry set. (This is exactly the `exec-flow-compilation.mmd` "Step 1 — per-form build_form plus typecheck-driven macro recognition+execution accumulating vec of ParsedEntry" then "Step 2 — single check_forms call.") A macro's *clause code* must therefore be in memory **before** the cluster's expand loop reaches a call to it. For in-module macros this means the defmacro's clause was JIT-codegened by an *earlier* cluster, OR — for an in-cluster forward use — the `MacroInMem` gap compiles it on demand during the expand loop (the gap fires from the expand loop, not from inside `check_forms`). Either way, **`check_forms` itself never triggers macro execution** — it runs over an already-fully-expanded entry set. The atomic-commit property is over that expanded set, unchanged.

This locates macro execution **outside** `check_forms` (in the orchestrator's expand loop) — which is exactly what `macro-expansion-ownership.md` §4.3's "Cleaner — keep the expand-and-build loop in `process_cluster` (int)" shape already commits to, and resolves the §4.3 "one subtlety the /dev waves must get right." The recognition *predicate* (is this head a macro? which clause?) is typecheck's, exposed for the orchestrator's expand loop to call; the *walk-and-execute loop* is the orchestrator's (int), driving the typecheck recognition predicate + the int `MacroExpander`. **`check_forms` receives post-expansion `Vec<ParsedEntry>` — consistent with the user's constraint #2** (typecheck takes already-built entries; cannot `build_form`).

So the foundation that the pressure-test collapsed resolves as: **macro recognition is typecheck's knowledge but runs in the orchestrator's pre-`check_forms` expand loop; macro execution is int's capability; `check_forms` stays a pure two-pass over fully-expanded entries.** This is precisely the `macro-expansion-ownership.md` §4.3 "second shape" — now grounded in the availability model rather than left as an open /dev choice.

> **One mechanism refinement vs the provisional `exec-flow-compilation.mmd`.** The diagram currently shows typecheck surfacing `MacroInMem` *from inside the check_forms region* (lines 88-108). Under the reconciled invariant, the `MacroInMem` gap fires from the **orchestrator's expand loop** (Step 1), before `check_forms` (Step 2). The recognition predicate typecheck exposes is called *by the expand loop*. The diagram's Step-1 note already says "typecheck-driven macro recognition+execution accumulating vec of ParsedEntry" — so the fix is to move the `opt macro head recognised` blocks (lines 88-108) to sit clearly inside Step 1's expand loop, not straddling the `check_forms` call. This is a diagram-clarity cascade, not a mechanism change. `/arch` updates `exec-flow-compilation.mmd` when this deep dive's recommendation is approved.

---

## 4.4 Worked example — macro body calls a defn helper (S76 W-Macro concrete-trace confirmation)

> **THE DISPROOF THAT DROVE THE LOCKED DECISION — retained verbatim (2026-06-03).** This trace is the load-bearing evidence behind §0. It proved that a macro clause body calling a plain same-module `defn` helper does NOT work as-built (empty GOT slot at expansion → crash/UB; `stdlib/defs.cl:20-22` workaround). The deep dive concluded "Option (f) needs a net-new step to codegen the clause's defn-callee closure." The user's subsequent pressure-test asked the harder question — *should a macro clause be allowed to call a same-module defn helper at all?* — and the round-trip-safety analysis (§0.3) answered **no**: permitting it breaks `regenerate_backing_file`. So the locked decision **forbids** the very scenario this section traces, rather than building the net-new wiring to support it. **The "VERDICT" and "what Option (f) must ADD" conclusions below are SUPERSEDED**: the scenario is a *rejected program* under §0 (§0.8), and the `block_for_macro_codegen` wiring is **deleted, not wired** (§0.7). Read this section as *why the simpler model lost* — the empty-slot failure is the symptom; the round-trip-safety constraint is the diagnosis; the dependency-only expansion rule (§0.1) is the cure.

`/sprint` commissioned a source-grounded confirmation of the canonical §9.8 promise against a scenario the option-space analysis (§2) and the §4.2/§4.3 cost statements did **not** isolate: a macro whose **clause body calls a plain `defn` at expansion time**. The earlier text reasons about *macro*-dependencies (`MacroInMem`, the macro-uses-macro forward chain), but the macro's compile-time dependency here is an ordinary function. This section traces it against the *actual* hot-path source and states a verdict. **It is honest about a real gap the source has today.**

### The scenario

```clojure
(defn helper [x] …)                  ; plain function
(defmacro m [a] … (helper a) …)      ; m's CLAUSE BODY calls helper AT EXPANSION TIME
(defn f [y] (m y))                    ; later defn whose body uses macro m
```

The claim: `helper` compiles → `m`'s clause compiles (body calls compiled `helper`) → `m` executes to expand `(m y)` inside `f` → `f` typechecks/commits. Chain `helper → m → f` is linear.

### What the source actually does (the names the design doc aspirated, vs the names that exist)

First, a calibration the prior W-Macro passes missed. The mechanism §6 names — `priority_boost_jit`, `wait_for_inmem`, "the `MacroInMem` gap fires" — **do not exist as code**. `MacroInMem` is a `ResolutionGap` variant (`crates/cranelisp-types/src/error.rs:361`) whose rustdoc *describes* a `priority_boost_jit(fq) + wait_for_inmem(fq)` flow, and `block_for_macro_codegen` exists in `src/scheduler.rs:669` — **but it has no live call site** (grep: referenced only in two comments, `src/worker.rs:2413` and `:2501`). The variant is **not raised on the in-module path at all** (its rustdoc: "Produced *exclusively* by `cranelisp_frontend::expand`" — the inert skeleton `macro-expansion-ownership.md` retires). The real in-module mechanism is different and simpler:

- **Recognition** is module-wide via `separate_macros` (`src/worker.rs:1178`) + `register_macro_in_module` (`:1305`) in Pass 1 — exactly Option (c)/(f) as designed. ✔
- **Execution-on-demand** is NOT a scheduler gap. It is the `MacroResolver::resolve_macro` impl (`src/worker.rs:466`): when `expand_sexp_recursive` (`src/expander.rs:354`) hits a macro head whose clause code is absent (`has_code_ptr` false, `:489`), the resolver **synchronously compiles the clause inline** (`compile_macro_with_state`, `:498`) *during* the expand call. No priority queue, no `wait_for_inmem`, no worker hop. The "gap" is a direct recursive compile.

So the in-module model is: **Pass-1 signature recognition + synchronous-inline clause compile on first reference.** This *is* Option (f) in spirit (recognition pre-pass + execution-on-demand), but the execution half is a direct call, not the scheduler-mediated boost the §6 prose describes. **§6's `priority_boost_jit`/`wait_for_inmem` is aspirational naming for a mechanism that, in-module, is a synchronous inline compile.** (For the cross-module FQ half — §3 — the scheduler IS involved via `block_for_typecheck`; that half is accurately described.)

### The decisive defect: `helper` is NOT compiled when `m`'s clause executes

Trace the canonical ordering (`helper`, then `m`, then `f`) through Pass 2 (`pass2_check_bodies_with_expansion`, `src/worker.rs:1363`), source-order:

1. **`helper` (Regular form)** → `process_regular_form` (`:1404`) → `try_expand_sexp` (no macros) → built AST accumulated into `expanded_program` (`:1487`). **`helper` is NOT codegen'd here.** Regular-defn codegen is deferred to `finalize_module` (`:1252`) / the nice worker — Pass 2 only *typechecks bodies into* the cluster and accumulates. `helper`'s GOT slot is assigned (Pass 1) but **empty**.
2. **`m` (Defmacro form)** → `compile_macro_if_needed` (`:2394`) → `compile_macro_clause_inline` (`:2510`) → `inline_jit_codegen_for_names(&[m's clause defn])` (`:2584`). The clause body's call to `helper` is emitted as a **GOT-indirect** load+call through `helper`'s per-module GOT slot (`__cranelisp_got_{M}`, backend `compile_to_module`, `crates/cranelisp-backend/src/lib.rs:442-449`). Codegen of the clause does **not** require `helper`'s code to exist — only its slot *index*. `compile_macro_if_needed` even walks `m`'s transitive callees (`collect_transitive_uncompiled_deps`, `:2415`) and finds `helper` uncompiled — but it only calls `notify_inmem_codegen_complete(helper, false)` (`:2425`); **it does not compile `helper`.** The comment at `:2411-2414` claims "the actual compilation is handled through the scheduler's normal priority codegen path (`block_for_macro_codegen`)" — but `block_for_macro_codegen` is dead (no call site). So `helper` remains uncompiled; its GOT slot stays empty.
3. **`f` (Regular form)** → `try_expand_sexp` → `expand_sexp_recursive` hits `(m y)` → `resolve_macro` finds `m`'s clause compiled → `invoke_clause` (`src/expander.rs:119`) → `invoke_jit_protected` runs `m`'s clause body → the clause's GOT-indirect call to `helper` **loads an empty slot and calls through it.** `helper`'s code was never written to its slot. **This is a NULL/garbage indirect call at macro-expansion time — a crash or undefined behaviour, not a clean result.**

**The trace fails at step 3.** The non-cyclic, linear chain `helper → m → f` does **NOT** work under the source as-built, because the on-demand compile path (`resolve_macro` → `compile_macro_with_state`) compiles **only the macro clause**, never the macro clause's own *function* callees. There is no function-resolution gap analogous to the macro `MacroInMem` gap; the dead `block_for_macro_codegen` was the intended-but-never-wired mechanism for exactly this.

### In-tree confirmation: `/stdlib` already hit this and worked around it

This is not a hypothetical. `stdlib/defs.cl:20-22` carries an explicit comment:

> ";; def and def- inline the name-mangling (append "-def" to symbol name) / ;; rather than calling a separate make-def-name helper, **because defn-defined / ;; helpers are not available during macro compilation (Phase 3 vs Phase 4).**"

`stdlib/core/syntax.cl:31` defines exactly such a helper (`make-def-name`) and `stdlib/core.cl:7` exports it — but the `def`/`def-` macros that *want* it instead inline the `str-concat`-based mangling into their clause bodies (`defs.cl:25,35`) to avoid calling it. The user-proxy skill encountered the precise scenario, found it broken, and routed around it. **The §9.8 promise, as traced, is not met by the current source.**

### The three sub-orderings of `helper`

Source-order does not rescue the linear chain, because the failure is *not* an ordering problem within Pass 2 — it is that **regular-defn codegen is deferred past Pass 2 entirely** while macro-clause codegen happens *in* Pass 2:

- **`helper` before `m` (canonical).** As traced: `helper` typechecked-into-cluster but not codegen'd; `m`'s clause codegen'd; `m` executes against `helper`'s empty slot → **fails**.
- **`helper` between `m` and `f`.** `m`'s clause is codegen'd *before* `helper` is even seen in Pass 2; `helper`'s slot still empty when `m` later executes inside `f` → **fails identically**. (Recognition of `m`'s head is fine — Pass 1 registered it; the failure is execution-time, not recognition-time.)
- **`helper` after `f`.** `helper`'s slot empty throughout; `m` executes inside `f` before `helper` is processed at all → **fails identically**.

All three fail at the same point and for the same reason: **deferred regular-defn codegen vs in-Pass-2 macro-clause codegen.** There is no ordering of source forms that makes a `defn` callee's *code* present at the moment a macro clause executes, short of compiling that callee on demand — which the source does not do.

### The atomic-commit interaction (Decision 44) — and a double-typecheck

`check_program_compat` (`src/worker.rs:221`) now runs the **active** staging path `process_cluster_with_staging` (`:248`, Wave 3b-2c.3 — FIXME 0179 landed; cluster mode is the hot path). So typecheck *does* stage-then-commit atomically. But macro-clause compilation interleaves *two* `check_program_compat` calls with the final cluster check:

- **Typecheck #1 of `m`'s clause:** `compile_macro_clause_inline` (`:2538`) calls `check_program_compat` on **just the synthesized clause defn** — its own staging frame, committed to live immediately, mid-Pass-2. This is what makes the clause executable.
- **Typecheck #2 (the cluster):** `finalize_module` (`:1271`) calls `check_program_compat` over the **whole expanded program** (`helper` + `f`'s expanded body + exprs) — a *second* staging frame.

So **`helper` is typechecked once** (in the cluster pass #2; its body is not re-checked for the clause path since the clause references it by name only). But the **macro clause defn is typechecked twice** if it ever reaches the cluster pass — and more importantly, the macro-clause's commit (#1) lands on **live**, *outside* the cluster's atomic frame (#2). This is precisely the §4.3 hazard the recommendation flags: macro codegen (and here its driving typecheck #1) happens **mid-cluster, against live, before the cluster's atomic check.** Under the as-built source the D44 atomic-commit property is **already scoped, not intact**: a macro clause committed in #1 does not roll back if the cluster fails in #2. This contradicts §4.3's claim that "`check_forms` itself never triggers macro execution … the atomic-commit property is over [the expanded] set, unchanged" — **today it is not, because clause typecheck+codegen commits to live before the cluster check.** Option (f)'s §4.3 invariant is a *target*, not a description of the current source.

### The cyclic variant — where (and whether) it is rejected

For the macro-uses-macro cycle (`m`'s body uses macro `m2`; `m2`'s body uses `m`), the relevant detector matters:

- `detect_cycle_locked` (`src/scheduler.rs:639`) walks the **module-level `blocked_on` edge** set by `block_for_typecheck`. It catches **cross-module mutual imports** (Decision 0030) — NOT intra-cluster macro-uses-macro cycles. There is **no intra-cluster macro-cycle detector.**
- The only intra-cluster bound is `EXPANSION_DEPTH_LIMIT = 100` (`src/expander.rs:15,359`). A cycle that manifests through *expansion* recursion (`expand_sexp_recursive` → `resolve_macro` → inline-compile a clause whose body expands the other macro → …) terminates with a "macro expansion depth limit exceeded" `MacroError` at depth 100 — a **bounded rejection, but a blunt one** (depth-limit error, not a "circular macro dependency" diagnostic).
- **However** — and this sharpens §4.2 — the inline clause-compile path (`compile_macro_clause_with_state`, `:609`) does **only `expand_quasiquotes`** on the clause body (`:628`), **not full macro expansion**. So a macro whose clause body *calls another macro* is not generally expanded during clause compilation at all; that call would reach the AST builder / typecheck as an unresolved name and fail there. The macro-uses-macro-in-body case is itself largely unsupported in the current source, independent of cyclicity. The "cyclic forward macro-uses-macro chain is rejected" claim (§4.2) is **true but for a different reason than stated**: not a `blocked_on` cycle walk (that's module-level), but either the depth limit (if it expands) or name-resolution failure (if it doesn't).

### VERDICT

**Option (f) does NOT handle the plain-fn-called-by-macro-body scenario as-is.** The trace disproves the linear-chain claim against the current source:

1. **Sub-question 1 (the function-resolution gap):** There is **no** function-resolution gap analogous to `MacroInMem`. The on-demand path compiles the macro *clause* only, never the clause's `defn` callees. The intended mechanism (`block_for_macro_codegen`) is **dead code**. A macro clause that calls a plain `defn` is codegen'd with a GOT-indirect to an **empty slot**; at expansion time the call goes through an uninitialised slot → crash/UB. Confirmed by `stdlib/defs.cl:20-22`'s explicit workaround.
2. **Sub-question 2 (atomic commit / double-typecheck):** Macro-clause typecheck+codegen runs **mid-Pass-2 and commits to live** (`compile_macro_clause_inline` → `check_program_compat` #1), *before* the cluster's atomic check (`finalize_module` → `check_program_compat` #2). D44 atomicity is therefore **already scoped today** — the §4.3 "intact" claim is a target, not the as-built reality. `helper` is single-typechecked; the macro clause is the double-checked entity. No source-ordering of `helper` rescues the chain (all three orderings fail at the same execution-time empty-slot call).
3. **Sub-question 3 (cyclic rejection):** Intra-cluster macro cycles are **not** caught by `detect_cycle_locked` (that is module-level, Decision 0030). They are bounded by `EXPANSION_DEPTH_LIMIT` (if they expand) or fail name-resolution (clause compile does quasiquote-only, not macro expansion). Bounded and terminating, but via a blunt depth-limit error, not a dedicated cycle diagnostic.

**What Option (f) must ADD to handle the scenario** (this is a genuine addition, not a re-description):

> **(f) requires a function-dependency resolution step for macro-clause compilation: before a macro clause is executed, every `defn` in its transitive callee closure (within the cluster/module) must be codegen'd so the clause's GOT slots are populated.** Concretely, the dead `block_for_macro_codegen` path must be **wired live** (or replaced): `compile_macro_if_needed` / `resolve_macro`'s inline-compile must drive `inline_jit_codegen_for_names` over `collect_transitive_uncompiled_deps(m)` — the closure it already computes (`src/worker.rs:2415`) but currently only *notifies* about — **before** invoking the clause. This is the function-side twin of the macro `MacroInMem` boost. It is bounded by the same no-cycle constraint (a `defn` that transitively, through a macro, depends on `m` itself is the cyclic case).

**Impact on the recommendation, cost, and mechanism:**

- **Decision 1 (the (f)-vs-(a) recommendation) still stands**, but its **cost statement (§4.2) is now understated and must be corrected.** §4.2 bounds the cost to *macro-uses-macro* forward chains. The real, larger cost is: **(f) additionally requires on-demand compilation of a macro clause's *function* callees** — a step the source does not perform today and which the dead `block_for_macro_codegen` was meant to provide. This is more than "name an existing mechanism" (the Principle 6 claim in §4.1): the function-callee-codegen-before-clause-execution step is **net-new wiring**, even if it reuses `inline_jit_codegen_for_names` + the already-computed callee closure.
- **Option (a) (use-after-def only) does NOT escape this defect.** Even under (a), `f` follows `m` follows `helper` in source order, yet `helper`'s *code* is still absent when `m`'s clause executes (deferred regular-defn codegen). So **(a) needs the same function-callee-codegen addition** — the defect is orthogonal to the recognition rule. This is an important correction to the §2/§7 framing, which treats (a) as "strictly simpler, fully predictable": (a) is simpler for *recognition*, but the *execution* defect (clause's defn callees uncompiled) is identical under (a) and (f).
- **§4.1's Principle-6 "minimum mechanism / = current as-built behaviour" claim is overstated** for this scenario: the function-callee path is not as-built. The macro-*recognition* half is as-built; the macro-*clause-execution-against-defn-callees* half is not.
- **The `MacroExpander` boundary type (§6) is unaffected** — the addition is interior to int's expand+compile orchestration (which `defn`s to codegen before invoking a clause), carrying no new `cranelisp-types` type. The §4.3 "second shape" pinning still holds; this trace *adds* a requirement *within* that shape (the expand loop must codegen clause-callee `defn`s before invoking).

**The target facade reproduces the defect, not just the source.** This is not merely an as-built gap that the W-Macro target design fixes incidentally. `facades/int.md:1216-1219` (the *as-designed* gap-handling rationale, the live int facade) explicitly commits to the very behaviour that causes the failure:

> "The orchestrator owns the **macro-vs-fn discrimination**. After `wait_for_typecheck_symbol` completes, it peeks at the entry: only forces a JIT (`priority_boost_jit` + `wait_for_inmem`) if the entry actually IS a macro with missing code. **Functions are NOT speculatively JIT-pushed — the function will be JIT'd when its caller is processed.** This avoids yanking a function ahead of pending priority work for code that expand never actually needs."

That rationale holds for a *function* caller (which runs at execute time, after all codegen). It is **false for a macro-clause caller**, which runs *during expansion* — before its callees are codegen'd. "code that expand never actually needs" is exactly wrong here: expand DOES need the clause's `defn` callees, because the clause executes them. **So the W-Macro target design, as currently stated in `facades/int.md`, would reproduce the defect** unless it is amended to JIT a macro clause's `defn`-callee closure when (and only when) forcing the clause's own code into memory for expansion. This is the manifestation site the fix lands at: when the orchestrator does `priority_boost_jit(macro_fq) + wait_for_inmem(macro_fq)` for a `DefKind::Macro` entry, it must additionally boost+wait the macro's transitive `defn`-callee closure (the function-side twin of the macro boost), bounded by the same no-cycle constraint.

> **CASCADE FLAG (for /arch on user approval of decision 1):** `facades/int.md:1216-1219` "Gap design rationale" needs an amendment — the "Functions are NOT speculatively JIT-pushed" clause must carry an exception for macro-clause callees (a clause's transitive `defn` callees ARE boosted when the clause is forced in-mem for expansion). This is the as-designed correction that closes the §4.4 defect; it lands when /dev wires the step. Filed here as the cascade target; not edited pre-approval (the deep-dive recommendation is still pending user sign-off).

This worked example is filed as the durable record of the gap. Per the project's defect-handoff protocol, `/sprint` should route a `/qa` narrow integration test reproducing the empty-slot failure (the `stdlib/defs.cl` workaround is the existing real-world instance; a minimal repro is `helper`/`m`-calls-`helper`/`f` as above). The fix is `/dev` (int) wiring the function-callee codegen step (+ the `facades/int.md` rationale amendment above); it is **not** a spec change (the §9.8 promise is the intended behaviour — the source must be made to meet it).

---

## 5. The spec change — FINALIZED for /spec (LOCKED, 2026-06-03)

> **This is the canonical `/arch`-authored proposal text.** It matches the locked decision (§0) exactly and supersedes the Option-(f) text that earlier occupied this section (preserved in git). `/spec` commits the actual spec edits; `/arch` does not edit `spec/`. FIXMEs 0005/0006/0007 carry pointers here. The locked decision settles three normative changes: (1) defmacro-before-use + dependency-only expansion references (§9.3.4, §5.13.2); (2) the three-pass model + dropping the same-module-helper claim (§9.8, §9.12); (3) FQ macro references folded into Pass 1 (§8.5.1 + new §9.3.6). REPL ≡ batch by construction.

### 5.1 §9.3.4 Module-Wide Availability → rename "Macro Availability and Definition Order"; rewrite (FIXME 0005)

Strike the current text ("extracts and compiles all `defmacro` forms in a pre-pass … MAY be used before its `defmacro`"). Recommended normative text:

> **A macro MUST be defined before it is used, in source order.** Within a module (and within a REPL `(begin …)` cluster), a `defmacro` is available only to forms that *follow* it. A use of a name that appears textually before its `defmacro` is **not** a macro call: it is an ordinary reference that passes through to the AST builder, and fails name resolution there if the name is otherwise undefined. (This is the *defmacro-before-use* rule; it is the same rule whether the code runs in the REPL or in a batch file — see §5.13.2.)
>
> **A macro's expansion may reference only:** (a) definitions in modules that are **dependencies** of the macro's defining module — i.e. modules typechecked before it (the compiler typechecks-and-compiles such a dependency just-in-time when an expansion first needs it; per §8.5.1 lazy loading); and (b) **macros**, including macros defined earlier in the same module (macros are the compile-time layer and depend only on prior modules). **A macro's expansion MUST NOT reference a same-module non-macro definition** (a `defn`, `def`, `const`, `deftype` constructor, or trait method defined in the same module). Such definitions are processed *after* macro expansion (see the three-pass model, §9.12) and do not exist when the macro expands; a macro that needs a helper must place that helper in a dependency module, or inline the logic into the macro body.
>
> The module dependency graph is **acyclic**: a dependency typechecked before a module cannot in turn depend on that module.

Rationale to include (normative consequence): forbidding same-module non-macro expansion-time references is what makes REPL session regeneration round-trip-safe — a session written back to a single batch file (`regenerate_backing_file`) recompiles identically, because every expansion-time reference resolves against a dependency, not against a same-file definition that would not yet exist at expansion in the regenerated file.

### 5.2 §5.13.2 REPL Input Boundary and `begin` Clusters — fix the internal contradiction (FIXME 0005/0006)

Strike the batch paragraph's claim (current line ~629) that "all `defmacro` forms are extracted and compiled in a pre-pass before other forms are processed (consistent with Clojure's module-wide macro model)" and the surrounding "macros within a module remain available throughout the module regardless of definition position." Replace with text consistent with §9.3.4's rewrite:

> Macros follow the **defmacro-before-use** rule (§9.3.4) in both REPL and batch: a macro is available only to forms that follow its `defmacro` in source order. A file is processed as one cluster, but unlike `defn`/`deftype`/`deftrait`/`impl` — which MAY forward-reference within a cluster (Pass-2/3 two-pass registration, §5.13.1) — a `defmacro` is part of the **compile-time layer** that runs *before* the cluster's non-macro forms are registered, so a forward reference to a macro is not resolvable as a macro. Macro **expansion** may reference dependency-module definitions and same-module macros, never same-module non-macro definitions (§9.3.4). This is the same rule in the REPL and in batch — there is no REPL-vs-batch macro-availability divergence.

The current batch example (current lines ~631-638) **must be reordered** so each `defmacro` precedes the form that uses it:

```clojure
;; Batch: defmacro precedes its use
(defmacro double [x] `(+ ~x ~x))
(defn f [x] (double x))

(defmacro triple [x] `(+ ~x ~x ~x))
(defn g [x] (triple x))
```

The REPL paragraphs (current lines ~608-625) are **already correct** under the locked rule — they already state defmacro-before-use (line 623: "a macro MUST be defined … before its first use"). They become the *uniform* statement: it was never REPL-specific. The §5.13.1 forward-reference rule continues to apply to non-macro definitions; macros are the exception (compile-time layer).

### 5.3 §9.8 + §9.12 — the three-pass model; drop the same-module-helper claim (FIXME 0006)

**§9.2.5 Macro Body Capabilities** — the current bullet "Calls to any function or macro visible in the macro's defining module scope — this includes functions defined earlier in the same module …" must be corrected: a macro body's *expansion-time* calls may reach **dependency-module** functions and **same-module macros**, NOT same-module non-macro functions. (The bullet conflates "visible in scope" with "available at expansion time" — only dependencies and macros are the latter.)

**§9.12 Bootstrapping Order** — replace the two-pass "Pass 1 type registration / Pass 2 sequential compilation" narrative with the **three-pass** model:

> A module is compiled in three passes:
>
> 1. **Pass 1 — Recursively typecheck `defmacro`s and expand all macro calls** (both unqualified and qualified `module/macro`). Dependency-module forms a macro clause needs are typechecked-and-compiled just-in-time during this pass. A macro generated by expansion (e.g. via `def` → `(begin (defn …) (defmacro …))`) is itself typechecked and compiled in this pass and becomes available to subsequent expansion; expansion runs to a fixed point. This is the compile-time layer.
> 2. **Pass 2 — Register non-macro signatures** of the fully-expanded form set (including macro-generated definitions), so the module's `defn`/`deftype`/`deftrait`/`impl` definitions may forward-reference one another (§5.13.1).
> 3. **Pass 3 — Type-check non-macro bodies** against the complete registered signature/impl set, and commit.
>
> Because Pass 1 runs before Passes 2–3, the module's own non-macro definitions do not yet exist when a macro expands — this is **why** a macro's expansion cannot reference a same-module non-macro definition (§9.3.4): the restriction is a structural consequence of the pass order, not a separate rule the compiler must police.

**Drop** the "ordering ensures" claims that no longer hold; **replace** specifically the bullet "Macro bodies can call helper functions defined earlier in the file" with: *"Macro bodies may call functions defined in dependency modules, and may use macros defined earlier in the same module."* Keep "User code can use all macros defined above it" (true — defmacro-before-use). Drop "Macro bodies can reference all type constructors (from Pass 1)" for same-module constructors (same-module constructors are Pass-2/3); a macro that needs a constructor at expansion time references one from a dependency module. Update the `[Tested …]` annotations as `/spec`/`/qa` see fit; the `macro_uses_another_batch` test should be re-examined against the rewritten rule.

(Note: the current `## 9.8` heading is "Hygiene." The locked three-pass model lands in **§9.12 Bootstrapping Order** + the §9.2.5 capability correction; the FIXME-text references to "§9.8" denote the *bootstrapping/availability* surface, which in the present spec numbering is §9.12. `/spec` places the three-pass text where the spec's numbering puts bootstrapping order.)

### 5.4 §8.5.1 + new §9.3.6 — authorize FQ macro references (FIXME 0007)

Adopt FIXME 0007's recommended **both**, folded into Pass 1:

- **§8.5.1 (Module-Qualified Names)** — extend the lazy-load paragraph: *A qualified name may resolve to any kind of symbol, including a macro. When the resolved symbol is a macro, the compiler invokes its expansion at the qualified call site, just as for a bare-name macro. Lazy loading applies: a qualified macro reference may trigger registration and typechecking-and-compilation of its defining module.*
- **new §9.3.6 "Qualified Macro References"** — *Macros may be invoked through qualified names (`module/macro-name`) without an explicit `import`. A qualified macro reference is resolved during macro expansion (the compile-time pass): the compiler lazy-loads, typechecks, and compiles the referenced module just-in-time (per §8.5.1), then expands the macro. Qualified macro references are not constrained by source order within the referring module — they target a dependency module, which is always typechecked before the referring module (the dependency graph is acyclic). There is no syntactic distinction between a qualified macro call and a qualified function call; the distinction is made when the compiler resolves the entry.*

This is the cross-module half of the model and is folded into Pass 1's just-in-time dependency compilation (§9.12). It is independent of the in-module defmacro-before-use rule (a dependency module's macros are always available, since the dependency is compiled first).

### 5.5 §9.14 Limitations — update item #2

Replace the current item #2 ("REPL ordering … In batch mode, macros are module-wide (see §9.3.4)") with: *"**Define-before-use for macros (both REPL and batch).** A macro must be defined before it is used in source order. A macro's expansion may reference dependency-module definitions and same-module macros, but not same-module non-macro definitions (§9.3.4, §9.12)."* The batch-vs-REPL divergence is removed (the rule is uniform).

### 5.6 Clojure-comparison disposition

Cranelisp **diverges intentionally** from Clojure's module-wide macro availability: Cranelisp requires define-before-use for macros, in both REPL and batch, as a deliberate consequence of (i) the form-by-form / three-pass compile model and (ii) REPL-session round-trip safety (a regenerated single-file session must recompile identically — only a dependency-only expansion rule guarantees this). Where the current spec text invokes "consistent with Clojure's module-wide macro model," strike it. The §5.13.2 "Why explicit clustering?" rationale (ML-family vs Haskell-family precedent) stands for *non-macro* mutual recursion via `(begin …)`; macros are the compile-time-layer exception and follow define-before-use.

---

## 6. The resulting W-Macro mechanism (confirms `macro-expansion-ownership.md`, with §4.3 pinned)

> **SUPERSEDED by §0.7 (2026-06-03 lock).** The ownership split below (recognize=typecheck, execute=int via `MacroExpander`, build+re-classify in int's expand loop, fixpoint in `process_cluster`, raw-`Sexp` return) **carries forward unchanged** — but the "net-new step to codegen the clause's transitive `defn`-callee closure" (the §4.4 addition) is **withdrawn** (§0.7): the locked decision forbids same-module non-macro expansion references, so there is no same-module `defn` callee to compile; clause callees are dependency forms (Pass-1 just-in-time) or same-module macros (Pass-1). The `block_for_macro_codegen` path is **deleted, not wired**. Read §0.7 for the canonical pinned mechanism.

Option (f) **confirms** the provisional ownership split and **pins the one open interior choice**:

- **Who recognizes:** typecheck — exposes the recognition predicate (head → is-macro? + clause match) over the symbol-table view (Pass-1 signatures). Module-local per Principle 17.
- **Who compiles (macro clause code):** the backend, driven by the orchestrator. **NAMING CORRECTION (§4.4):** `priority_boost_jit` / `wait_for_inmem` are *aspirational* names — they do not exist as code. In-module, the as-built path is a **synchronous inline clause compile** inside `MacroResolver::resolve_macro` (`src/worker.rs:466` → `compile_macro_with_state` `:498`), not a scheduler boost; the `MacroInMem` `ResolutionGap` variant is not raised on the in-module path and `block_for_macro_codegen` (`src/scheduler.rs:669`) is **dead code** (no call site). The scheduler IS involved for the **cross-module FQ** half (§3, via `block_for_typecheck`). **Per §4.4, this compile step must be extended to also codegen the clause's transitive `defn`-callee closure before the clause executes** — the net-new requirement the concrete trace surfaced.
- **Who executes:** int, via the injected `&dyn MacroExpander` (`cranelisp-types`), over `src/expander.rs`'s invocation core + `src/marshal.rs`. Returns a raw `Sexp`.
- **Who builds + re-classifies:** int's expand loop calls `cranelisp_frontend::build_form` on the result (keeping `build_form` out of typecheck per BC §2); nested macros and structural results re-enter the expand loop's fixpoint; the fully-expanded `Vec<ParsedEntry>` then feeds one `check_forms` call.
- **Where the fixpoint sits:** the orchestrator's expand loop in `process_cluster` (int) — **resolved as `macro-expansion-ownership.md` §4.3's "second shape," now grounded** (§4.3 above). NOT inside `check_forms`.
- **What `check_forms` takes:** post-expansion `Vec<ParsedEntry>` — consistent with the constraint that typecheck cannot `build_form` and takes already-built entries.
- **What the `MacroExpander` callback returns:** a raw `Sexp` (`Result<Sexp, MacroInvokeError>`) — unchanged.

**Public-API delta:** none beyond what `macro-expansion-ownership.md` already authors — `MacroExpander` trait + `MacroInvokeError` enum in `cranelisp-types` (already present as `crates/cranelisp-types/src/macro_expander.rs`, untracked). The availability model adds **no new boundary type**; it settles *semantics* and *sequencing*, both of which manifest in spec text + BC invariants + the sequence diagram, not in code types. The recognition predicate typecheck exposes is a typecheck-internal surface called by int's expand loop — its exact signature is `/design (typecheck)`'s interior (FIXME 0245), but it carries no new `cranelisp-types` type (it returns macro-vs-fn + clause index, expressible with existing `DefKind` / `Symbol`).

---

## 7. FOR USER REVIEW — decisions to confirm

> **RESOLVED by §0 (2026-06-03 lock).** These five review items have been decided. The locked outcomes: **(1)** NOT Option (f) and NOT Option (a) — the user drove the design to the **dependency-only + defmacro-before-use** rule (§0.1–§0.2), which is stricter than (a) on the same-module-helper axis and removes the use-before-def question entirely. **(2)** REPL ≡ batch — confirmed, grounded in round-trip safety (§0.3) rather than cluster-granularity framing. **(3)** FQ macro references — authorized, folded into Pass 1 (§0.4). **(4)** D44 reconciliation — the expand-loop-before-`check_forms` shape is confirmed as the locked design; D44 intact over the Pass-2/3 layer (§0.5). **(5)** the `macro-expansion-ownership.md` mechanism stands, minus the withdrawn `defn`-callee-codegen addition (§0.7). The items below are retained as the review framing that was put to the user; §0 records the answers.

`/sprint` relays the following to the user before `/spec` or `/dev` act. **Decision (1) is a normative language change.**

1. **[LANGUAGE CHANGE — normative spec edit] In-module macro availability rule.** Confirm **Option (f)** — recognition is cluster-wide (Pass-1 signatures), execution is on-demand within the cluster, so **use-before-def works as the common case (Clojure-like)** but a cyclic forward macro-uses-macro chain is rejected and the convenience is best-effort, not guaranteed. The always-reliable subset is use-after-definition. **Alternative: Option (a)** — use-after-definition *only*, everywhere (simpler *recognition*, fully predictable, batch/REPL identical, but drops Clojure-style module-wide macros as an intentional divergence). `/arch` leans (f) because it matches the as-built source, the provisional mechanism, and the spec's stated Clojure-parity intent — but (a) is a legitimate simplification. **COST CORRECTION (§4.4 concrete trace):** the original cost statement understated the work. A macro whose clause body calls a plain `defn` helper at expansion time does **NOT** work in the source today (empty-slot crash; `stdlib/defs.cl:20-22` workaround) — and **neither (f) nor (a) escape this**: both require a net-new int-side step that codegen's a macro clause's transitive `defn`-callee closure before the clause executes (wiring the currently-dead `block_for_macro_codegen` path). This is a `/dev` (int) fix, **not** a spec change — the §9.8 promise is the intended behaviour the source must be made to meet. The (f)-vs-(a) decision is unchanged by this; the correction is to the cost/effort, which is larger than §4.2 originally stated and is shared by both options.

2. **[LANGUAGE CHANGE — normative] REPL/batch unification.** Confirm that macro availability is stated **uniformly as cluster-scoped** — a file is one cluster (module-wide), a bare REPL input is a one-form cluster (no forward), a `(begin …)` is a multi-form cluster (forward within). This removes the spec's current batch-vs-REPL macro divergence and the §5.13.2 internal contradiction. (Holds under both (f) and (a); the difference is only what "available" means within a cluster.)

3. **[LANGUAGE CHANGE — normative] FQ macro references authorized** (FIXME 0007). Confirm that qualified names `mod/macro` may resolve to macros, lazy-loading the defining module — the cross-module half of the mechanism, independent of (1).

4. **[ARCH — D44 reconciliation, no atomic-commit change] Macro execution sits in the orchestrator's expand loop, before `check_forms`.** Confirm the clarifying invariant (§4.3): the `MacroInMem` gap fires from int's expand loop (Step 1), `check_forms` runs over fully-expanded entries (Step 2). This pins `macro-expansion-ownership.md` §4.3's previously-open interior choice to the "second shape" and keeps D44's atomic-commit property unchanged.

5. **[ARCH — confirms prior] The W-Macro mechanism in `macro-expansion-ownership.md` stands** (two-jobs split, `&dyn MacroExpander` trait object, raw-`Sexp` return, structural re-entry option (a), frontend skeleton deleted). This deep dive confirms it and adds only the §4.3 pin + the diagram-clarity cascade (§4.3 note). No public-API change beyond the already-authored `MacroExpander` + `MacroInvokeError`.

**Routing once approved:** FIXMEs 0005/0006/0007 carry the refreshed `/arch`-recommended spec text → `/spec` commits. `/arch` cascades BC §2/§6 + `exec-flow-compilation.mmd` clarity fix. `/dev` (typecheck/int/frontend) implements per `macro-expansion-ownership.md` + this model. FIXME 0175 stays open (`resolution-designed-impl-pending`) until /dev lands.
