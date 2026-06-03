# Macro-expansion ownership — the two-jobs split (S76 W-Macro)

**Status.** Phase 3 design, resolving FIXME 0175. Implementation pending /dev waves (S76 W-Macro). User-arbitrated direction (S76 Phase 2); this doc formalizes it.

**Manifestation.** This is a cross-crate ownership commitment (frontend / typecheck / int), so it lives in `design/arch/`. The cascade lands in the canonical set (BC §1, §2, §6; `exec-flow-compilation.mmd`; `cranelisp-types::MacroExpander`). The typecheck-interior algorithm (walk order, fixpoint loop, re-classification mechanics) is `/design (typecheck)`'s to elaborate at `design/typecheck/macro-recognition.md` — filed as a FIXME.

---

## 1. The decision (not relitigated here)

FIXME 0175 surfaced an internal inconsistency: the facade put macro **execution** inside `cranelisp_frontend::expand`, but execution needs the JIT'd code address, the allocator, the runtime panic slot, and `libc` signal machinery — all forbidden to frontend by its dependency rule (BC §1: frontend depends only on `cranelisp-types`). The four options in 0175 were (a) a `cranelisp-marshal` bridge crate, (b) relocate marshal to types, (c) a callback on `expand`, (d) leave the real executor in `src/expander.rs` as today.

The user interrogated the factoring against source and ruled:

- **(a) `cranelisp-marshal` is REJECTED.** No new crate.
- The real executor today **is** `src/expander.rs` (`expand_sexp_recursive` walks + recognizes + executes via `invoke_jit_protected`). `crates/cranelisp-frontend/src/expand.rs::expand` is an inert skeleton that returns `Gap` for every macro head and is never on the hot path. The sequence diagram wrongly depicted frontend doing the expansion.
- **Target:** frontend keeps only syntactic work; **typecheck owns walk + recognize**; **typecheck calls back to int to execute** via an injected callback whose type lives in `cranelisp-types`; **typecheck handles further processing** of the expansion result (nested fixpoint + structural re-classification).

This doc formalizes that target and resolves the one open question (where structural expansion results re-enter).

---

## 2. Two jobs, cleanly separable

Macro expansion is two jobs that have been conflated:

| Job | What it needs | Where it belongs |
|---|---|---|
| **Walk + recognize** | Structural traversal of a form; symbol-table lookup of each head; macro-vs-fn discrimination; clause-arity matching; depth bound; quasiquote desugar | **typecheck** (already walks the cluster + resolves every head; `cranelisp-types` is sufficient) |
| **Execute** | The JIT'd clause's GOT address; `Sexp`↔heap marshal (allocator); runtime panic slot; `sigsetjmp`/`siglongjmp` (`libc`) | **int** (owns `src/expander.rs::invoke_clause` + `src/marshal.rs`; the only crate that may touch JIT + runtime + libc) |

The split is clean because the two jobs communicate through exactly two values: **down** = (macro identity, argument `Sexp`s, call span); **up** = the output `Sexp`. Neither value carries a type that inverts the dependency graph.

### 2.1 Frontend after the split — syntactic only

`cranelisp_frontend::expand` is **retired from the public boundary** (made private or deleted). Frontend keeps:

- `parse` — source → `Sexp`.
- `expand_quasiquotes` / `expand_quote_template` / `next_synthetic_span` — the standing public quasiquote API used by user-authored macros and REPL `/expand` (these stay; they are pure syntactic desugaring, no execution).
- `build_form` / `build_expr` / `extract_module_declarations` — `Sexp` → AST.

**The structural-walk skeleton in `crates/cranelisp-frontend/src/expand.rs` is DELETED, not kept private.** Recommendation + justification: the skeleton's entire job (walk children, recognize macro heads via `symbol_tables`, depth-bound, return `Gap`) is exactly the walk+recognize job that moves to typecheck. Keeping it private in frontend would mean two implementations of the same walk in two crates — a Principle 7 (single source of truth) violation and a guaranteed drift source. The quasiquote desugaring it calls (`expand_quasiquotes`) already lives in `crates/cranelisp-frontend/src/quasiquote.rs` and stays there as the public syntactic API; typecheck calls it (or, more precisely, int calls it during parse — see §5) before the walk. `ExpansionError` retires with the skeleton (its `Gap` carrier role moves to `CheckError::Gap`, which typecheck already has; `MacroAborted` is replaced by `MacroInvokeError` on the callback). The `EXPANSION_DEPTH_LIMIT` const moves to typecheck's interior (the depth bound is now typecheck's loop invariant).

### 2.2 Typecheck after the split — recognize + drive

Typecheck's `check_forms` already iterates the cluster's `ParsedEntry` list and resolves every head symbol against the symbol-table view, so it already distinguishes macro from fn (a head whose entry is `DefKind::Macro`). The within-form descent to find macro heads is added to typecheck's walk. On recognizing a macro head whose clause code is in memory, typecheck calls back through the injected `MacroExpander`. The returned `Sexp` is re-processed (§4).

This is consistent with Principle 17 (module-locality): macro-head resolution uses the **`cranelisp-types` resolution primitive** (`cranelisp_types::resolve_macro_head`) — shape 1 (unqualified short-name → current-module view → one Import hop) or FQ lookup (shape 2). No new module-set iteration is introduced — the bare-name "probe every module" loop in the retired frontend skeleton (`lookup_macro_fq` iterating `symbol_tables.iter()`) is **eliminated**, replaced by the principled current-module-view lookup. This is a net Principle-17 improvement.

**Resolution-primitive fold-in (2026-06-03).** The name-resolution mechanism is **types-owned**, not typecheck-resident: `cranelisp_types::resolve_macro_head` is a pure query over `symbol_tables` + `module_aliases`, generic `<C, L>`, no `CheckState`. The caller supplies the first-hop `View`: int's Pass-1 recognition passes the **committed** view (`View::single(live)`); typecheck's body-resolution passes its staging ∪ live view. The consequence for this ownership split is sharper than §1's original framing: macro **recognition leaves typecheck's public surface entirely** (it is a `cranelisp-types` query both int and typecheck call) — typecheck's contribution is the within-form descent that calls the primitive during its Pass-2/3 walk, plus its `resolve_*` family becoming thin callers of the same primitive. int's Pass-1 expand loop calls `resolve_macro_head` directly, with **zero int→typecheck dependency for recognition**. See `macro-availability-model.md` §0.9 + `bounded-contexts.md` §7 "Resolution primitive".

### 2.3 Int after the split — execute via the injected callback

`int` implements `MacroExpander` over its existing invocation core. `src/expander.rs`'s `invoke_clause` / `find_matching_clause` / `invoke_jit_protected` / `rewrite_spans` and `src/marshal.rs` move **behind** the trait impl — they stay in `int` (the only crate allowed the JIT+runtime+libc deps), but they stop being reachable as a free-standing `expand_sexp_recursive` walk. The walk (`expand_sexp_recursive`, `expand_macro_call_with_entry`, the `MacroResolver` trait) **deletes** — its walk responsibility moved to typecheck; only the per-invocation core (marshal + signal-protected call + span-rewrite) survives, wrapped by the `MacroExpander::invoke` impl. `int` constructs the impl and threads `&dyn MacroExpander` into each `check_forms` call (via `process_cluster`).

---

## 3. The callback boundary type

Authored in `crates/cranelisp-types/src/macro_expander.rs` (this change-set):

```rust
pub trait MacroExpander: Send + Sync {
    fn invoke(
        &self,
        fq: &FQSymbol,
        args: &[Sexp],
        call_span: Span,
    ) -> Result<Sexp, MacroInvokeError>;
}

#[non_exhaustive]
pub enum MacroInvokeError {
    Aborted   { fq: FQSymbol, message: String, span: Span },
    Malformed { fq: FQSymbol, message: String, span: Span },
}
```

**Why a trait object, not a fn handle.** The implementor (int's expander) holds session state — the symbol tables it reads clause GOT slots from, the per-call thread-local signal buffers. A `&dyn MacroExpander` carries that behind one stable vtable; a bare `fn` pointer would force int to thread the state through a closure capture and a `&dyn Fn(...)` — which is the same vtable cost with a less legible signature. The trait names the contract (`invoke`) and the error shape (`MacroInvokeError`) explicitly; that legibility is the deciding factor under Principle 2 (narrow interfaces).

**Why `Send + Sync`.** Decision 38 allows concurrent typecheck workers; each may recognize a macro and call back in parallel. The supertrait makes that safe by construction; the implementor's invocation core isolates per-call signal state (already thread-local in `src/expander.rs`).

**Why the result is a raw `Sexp`, not a classified product.** See §4 — the re-entry resolution.

**DAG proof (typecheck stays types-only).** `MacroExpander` lives in `cranelisp-types`. typecheck adds **no** dependency: it already depends on `cranelisp-types`, and `&dyn MacroExpander` is a `cranelisp-types` type. int already depends on `cranelisp-types` (to author the impl) and on typecheck (to call `check_forms`). No edge is added in the typecheck→int direction; the only new flow is a value (`&dyn MacroExpander`) passed *into* `check_forms` by int, which is the existing int→typecheck call edge. Frontend loses a responsibility and gains nothing. The graph is unchanged and acyclic:

```
cranelisp-types  ← frontend
       ↑         ← typecheck   (holds &dyn MacroExpander from types)
       └──────────  int        (impls MacroExpander; calls check_forms with it)
```

---

## 4. The open question — where structural expansion results re-enter

**The problem.** A macro can expand into a **structural** top-level shape, not just an expression. `def` splices to `(begin (defn …) (defmacro …))`; expansions can introduce new `defmacro`s. Today this is handled *above* typecheck in `src/worker.rs::process_regular_form` (`flatten_begin` → re-partition out `defmacro`s → register/compile them → build the rest). If recognition+execution move *into* typecheck's walk, the **result** of an invocation may need to re-enter form-classification (defmacro registration, begin-splice flattening), not merely continue as an expression.

**The resolution: (a) typecheck re-classifies structural results itself.** The callback returns a raw `Sexp`; typecheck re-walks it through the same per-form classification it already runs.

### 4.1 Why (a), grounded

**Grounded in the existing shape.** `process_cluster` already feeds `check_forms` a `Vec<ParsedEntry>`, and `check_forms` already classifies each entry (`Def`, `TypeDef`, `TraitDecl`, `TraitImpl`, `Macro`, `Constructor`) and runs two passes over them. A macro result that is `(begin (defn f …) (defmacro m …))` is, after `flatten_begin`, exactly a sequence of forms that `build_form` turns into `ParsedEntry::Def` + `ParsedEntry::Macro` — the *same* entries `check_forms` already handles. So "re-classify the result" is not new machinery: it is re-running the build_form → classify step that `check_forms` is built around, on the expansion output. The natural shape is: typecheck's walk, on a macro head, calls `invoke`, then `build_form`s the result into `ParsedEntry`s and **splices them into the cluster's pass** (Pass 1 registers any new signatures/macros; Pass 2 checks bodies). Nested macros inside the result are caught because the spliced entries are walked again — the fixpoint is the same loop.

> Note: this means typecheck calls `cranelisp_frontend::build_form` on the expansion result. typecheck already depends on `cranelisp-frontend`? **No** — and it must not. See §4.3 for the resolution: `build_form` runs in int (the orchestrator), invoked through the callback's surrounding loop, OR the expansion result is built in int and handed back. The cleanest shape keeps the build step in int. This is the one subtlety the /dev waves must get right; the recommendation is **option (a) with the build step orchestrated by int** (§4.3).

**Grounded in Principle 17 (module-locality).** Re-classification is current-module work: a spliced `defmacro` registers into the current module's staging table via `ctx.current_symbol_table_mut()`; a spliced `defn` registers its signature the same way. No module-set iteration; no cross-module reach. Option (b) — signalling back to int's form pipeline to re-run `process_regular_form` — would move the re-classification *out* of the cluster-atomic staging frame, re-introducing the above-typecheck split that Decision 44 collapsed. That regresses Principle 17's "the `SymbolTableAccess` choke point only buys atomicity if every read and write flows through it": a `defmacro` registered by int's pipeline outside the staging frame is a direct-live write mid-cluster.

**Grounded in Decision 44 (cluster-atomic orchestration).** The whole point of Decision 44's third amendment is that the cluster's signature-registration and body-checking live in **one** `check_forms` stack frame against orchestrator-owned staging, committed atomically. A macro that splices a `defmacro` produces a new symbol that belongs to *this cluster* — it must register into *this cluster's staging*, so that if the cluster later fails, the spliced macro vanishes with it (live-table byte-identical-on-failure invariant, BC §2 invariant 2). Option (b) breaks this: int's pipeline re-running would either commit the spliced macro to live immediately (violating atomicity) or need its own staging frame (duplicating Decision 44's machinery outside typecheck). Option (a) keeps the spliced form inside the same staging frame — atomicity holds by construction.

**Grounded in Principle 6 (complexity-budget).** Option (a) reuses `check_forms`'s existing classify-and-two-pass loop; it adds a splice point, not a new subsystem. Option (b) adds a typecheck→int signal channel (a second callback, or a richer return type carrying "these forms need re-classification"), plus a re-entrant `process_regular_form` that must itself manage staging. Option (c) (a bounded hybrid — typecheck handles expression results, signals back only for structural results) needs typecheck to *classify* the result anyway to decide which path — at which point it has done the work option (a) requires, so the signal-back buys nothing but a boundary crossing. (a) is the minimum mechanism.

### 4.2 Consequence for the callback signature

Because typecheck re-classifies the result itself, the callback returns a **raw `Sexp`** — `invoke(&self, fq, args, call_span) -> Result<Sexp, MacroInvokeError>`. A richer classified return (e.g. `Vec<ParsedEntry>`, or an enum distinguishing "expression" from "structural") would:

- force the **execution** side (int) to know about form classification, which is typecheck's job — inverting the responsibility the split just established;
- make `MacroExpander` carry `ParsedEntry` (a parse-time transient) across the boundary as a *return*, coupling the execution callback to the build_form output shape;
- duplicate the classification typecheck must do anyway when it re-walks (a macro result can *contain* macro calls at arbitrary depth, so typecheck re-walks regardless of what the top-level shape is).

The raw `Sexp` return is therefore not just adequate — it is the shape that keeps the two jobs from leaking into each other. The macro-vs-fn discrimination, the begin-flatten, the defmacro re-partition, and the nested-fixpoint all stay on typecheck's side of the boundary; int's side does exactly one thing — turn (identity, args) into one output `Sexp`.

### 4.3 The build_form subtlety (for /dev (typecheck) + /dev (int))

typecheck must NOT depend on `cranelisp-frontend` (BC §2 keeps typecheck on `cranelisp-types` only). So the `build_form` call that turns the expansion `Sexp` into `ParsedEntry`s cannot run inside `check_forms`. Two implementable shapes, to be settled in the /dev design wave (the FIXME to /design (typecheck) names this):

- **Preferred — int orchestrates the expand+build, typecheck drives the recognize+splice.** `check_forms` recognizes a macro head and surfaces it the way it already surfaces dependencies: but instead of a `Gap` that unwinds the whole call, the injected `MacroExpander` does the invoke **and** the int-side `build_form` of the result, returning… a `Sexp` (typecheck re-walks) — and typecheck calls a second tiny injected capability to build that `Sexp` into entries. This risks a second callback (build_form-as-capability), which Principle 6 disfavours.
- **Cleaner — keep the expand-and-build loop in `process_cluster` (int), make recognition a typecheck-surfaced `Gap`-like signal carrying the matched `fq` + args.** This is the shape the current `process_cluster` already has for `MacroInMem`: expand surfaces a need, int resolves it. The difference under this design is that **typecheck** (not the retired frontend skeleton) is the surfacer, and int's resolution is "invoke + build_form + re-feed", looping until no macro heads remain, *then* the two passes run on the fully-expanded `Vec<ParsedEntry>`.

The second shape is the recommended target: it keeps `build_form` in int (no frontend dep added to typecheck), keeps the callback a pure `Sexp→Sexp` execution primitive, and makes the fixpoint a `process_cluster` loop (where the existing retry envelope already lives). Under it, "typecheck owns walk+recognize" means typecheck owns the **recognition predicate** (is this head a macro? which clause matches?) exposed as a typecheck entry the orchestrator calls during the expand loop — NOT that the `Sexp`-walk literally runs inside `check_forms`'s two-pass body. This preserves the user's direction (recognition is typecheck's knowledge, execution is int's capability, frontend is syntactic-only) while honouring the no-frontend-dep and cluster-atomic constraints.

**This is the one item the /dev (typecheck) + /dev (int) design wave must pin precisely.** Both shapes satisfy the ownership split and the DAG; the choice is an interior factoring. The FIXME to /design (typecheck) carries it. The `MacroExpander` boundary type is identical under both shapes — which is why it is authored now and the interior factoring is deferred to the design wave without risk.

> **PINNED — DECISION LOCKED (2026-06-03, user-approved).** `design/arch/macro-availability-model.md` §0 settles this open choice to the **second (Cleaner) shape**, now grounded in the locked **three-pass / phase-by-dependency** model rather than the (superseded) Option (f):
> - **Pass 1 = the expand phase** runs in int's `process_cluster` expand loop *before* `check_forms`. Typecheck recognizes macro heads; int's `MacroExpander` callback executes the compiled clause; **dependency-module forms a clause needs are typechecked-and-compiled just-in-time** during this pass (pause-and-fetch). Expansion runs to fixpoint (nested macros + structural re-classification re-enter the loop). The fully-expanded `Vec<ParsedEntry>` then feeds one `check_forms` call.
> - **Passes 2 + 3 = `check_forms`** (its internal two-pass discipline over the fully-expanded *non-macro* forms).
> - **Decision 44 atomic-commit is intact** over the Pass-2/3 layer — and this is now a true statement of the *design*, not a "target," because the locked decision **forbids same-module non-macro expansion references** (§0.1–§0.3), which removes the same-module-clause-commit-to-live-mid-cluster hazard the §4.4 trace found.
> - The diagram (`exec-flow-compilation.mmd`) is cascaded to depict the three-pass (Pass-1 expand-with-just-in-time-deps → Pass-2 sigs → Pass-3 bodies).
>
> See `macro-availability-model.md` §0 for the locked decision and §0.7 for the canonical pinned mechanism.
>
> **The §4.4 "net-new `defn`-callee-codegen step" is WITHDRAWN by the lock (2026-06-03).** The §4.4 concrete trace correctly disproved the as-built handling of a macro clause calling a same-module `defn` helper (empty GOT slot → crash/UB; `stdlib/defs.cl:20-22`). Under Option (f) the fix was "codegen the clause's transitive `defn`-callee closure before invoking (wire the dead `block_for_macro_codegen`)." The **locked decision removes the case rather than fixing it**: a macro clause MUST NOT call a same-module non-macro definition (round-trip safety, §0.3), so the clause's callees are **dependency** functions (compiled by Pass-1 just-in-time dependency compilation) or same-module **macros** (compiled in Pass 1). There is no same-module-`defn`-callee-with-empty-slot case. The dead `block_for_macro_codegen` path is **deleted, not wired**. As-built calibration that still holds: in-module execution today is a synchronous inline clause compile in `MacroResolver::resolve_macro` (`src/worker.rs:466`); `priority_boost_jit`/`wait_for_inmem` are aspirational names not present as code; the cross-module FQ half does use the scheduler. The `MacroExpander` boundary type is unaffected — Pass-1 dependency-compile orchestration is interior to int.

---

## 5. What lands where (cascade map)

| Site | Change |
|---|---|
| `crates/cranelisp-types/src/macro_expander.rs` | **NEW** — `MacroExpander` trait + `MacroInvokeError`. Authored S76 W-Macro change-set. |
| `crates/cranelisp-types/src/resolve.rs` | **NEW** (resolution-primitive fold-in, 2026-06-03) — `resolve` / `resolve_macro_head` / `Resolved` / `ResolveError`. The types-owned name-resolution primitive both int (Pass-1 recognition, committed view) and typecheck (`resolve_*`, staging view) call. `ResolveError` relocated here from `cranelisp-typecheck`. |
| `crates/cranelisp-types/src/lib.rs` | Re-export `MacroExpander`, `MacroInvokeError`, `resolve`, `resolve_macro_head`, `Resolved`, `ResolveError`. |
| `crates/cranelisp-types/public-api.txt` | Regenerated (MacroExpander +22 lines S76; resolution primitive +~40 lines the fold-in). |
| `crates/cranelisp-typecheck/src/checker.rs` (+ `result.rs`) | (Note for /dev (typecheck)) `resolve_trait`/`resolve_type`/`resolve_constructor`/`resolve_qualified` re-pointed at `cranelisp_types::resolve` (thin callers projecting `Resolved`/`ResolveError` to kind-specific results); the typecheck-resident chain-walk copies + the local `ResolveError` definition retire; the `From<ResolveError> for CheckError` projection stays in `result.rs` (CheckError is typecheck-owned). /arch leaves the expectation here; /design (typecheck) pins, /dev lands. |
| `src/worker.rs` | (Note for /dev (int)) `SymbolTableMacroResolver` + `resolve_macro_definition` chain-walk retire; Pass-1 recognition calls `cranelisp_types::resolve_macro_head` over the committed view. |
| `bounded-contexts.md` §1 (frontend) | `expand` drops from the public boundary; `ExpansionError` retires; FIXME 0175 paragraph removed; invariant 6's "expand returns Gap" reframed as "frontend does no macro execution or recognition — only quasiquote desugar". Authored this change-set. |
| `bounded-contexts.md` §2 (typecheck) | typecheck gains the recognize role + the injected `MacroExpander` capability; new invariant. Authored this change-set. |
| `bounded-contexts.md` §6 (int) | int supplies the `MacroExpander` impl over its invocation core. Authored this change-set. |
| `facades/int.md` | `process_cluster` loop: the expand step is now int's invoke+build loop driven by typecheck recognition + the `MacroExpander` impl; the `src/expander.rs` / `src/marshal.rs` rows reframed (walk deletes; invocation core survives behind the impl). Authored this change-set. |
| `sequences/exec-flow-compilation.mmd` + `.svg` | Correct the wrong "Frontend ->> PW: Ok(Sexp) — expanded" depiction; show typecheck recognition + int `MacroExpander` callback. Authored this change-set. |
| `crates/cranelisp-frontend/src/lib.rs` rustdoc | (Note for /dev (frontend)) `expand` made private/deleted; skeleton deleted; quasiquote API stays public. /dev edits source; /arch leaves the expectation here + in BC §1. |
| `design/typecheck/macro-recognition.md` | (FIXME to /design (typecheck)) the typecheck-interior algorithm + the §4.3 interior-factoring choice. |
| FIXME 0175 | Annotated "resolution designed S76 W-Macro; implementation pending /dev" (kept open until /dev lands, per §6 below). |
```
