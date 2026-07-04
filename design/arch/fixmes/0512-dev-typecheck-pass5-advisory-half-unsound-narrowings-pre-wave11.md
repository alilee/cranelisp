---
number: 0512
target: /dev (cranelisp-typecheck)
filed_by: /sprint
filed_at: 2026-07-04
sprint_filed: 102
refers_to: crates/cranelisp-typecheck/src/ownership/{transfer.rs,fixpoint.rs,confinement.rs}; design/arch/ownership-inference.md §2.2/§4.2/§5, design/typecheck/ownership-inference.md §13.6(d)
status: open
---

# pass5 advisory-half unsound narrowings — MANDATORY pre-Wave-11 precondition

The Wave-8b soundness review found three unsound narrowings + one termination-hardening gap in the pass5 **advisory** facts. **None threatens the S102 seam**: the ABI-bearing half (`param_modes`/`result`, consumed by R3 at Wave 9 via `abi_eq`) is computed soundly; these are all in the advisory half (escape site-facts, `spark_ops`, provenance) which **no consumer trusts until Wave 11's backend mechanisms**. They are invisible to the empty golden diff + toggle-off witnesses because nothing consumes yet. **They MUST be fixed before Wave 11** (whether late-S102 push-through or S103) — each is the exact narrowing that becomes a use-after-free / double-free / data race once a mechanism lowers on it. Full evidence: `sprints/SPRINT.md` §Notes Wave-8b review entry.

## Blocker 1 — escape site-fact + `param_flow` narrow below truth for binding-mediated escaping fresh aggregates
`transfer.rs:268-282` (`Let`) walks each RHS `Neutral`; a fresh `VecLit`/`ConstrADT`/`Lambda` returns `Origin::Fresh` (`:310-317`). The `Let` soundness comment claims a later escaping use of the binding re-classifies through its origin — **but that fires only for `Root`/`Projection` origins, never `Fresh`**. Shape:
```
(defn keep [x] (let [box (Some x)] box))
```
→ `escapes=false` on a returned ADT (rule-1 escape truth), and `x.param_flow=Consumed` when truth is `IntoResult`. Manifestation: Wave-11 stack/region-allocates a returned value → UAF; and the false `Consumed` propagates interprocedurally → caller-side reuse UAF. The DIRECT shape `(defn keep [x] (Some x))` is correct AND tested; the binding-indirected shape is the bug and is UNTESTED. Mode vector stays `Owned` (no ABI double-free). **Fix**: re-classify escape/flow for binding-mediated escapes (a returned/stored `Fresh` binding whose construction consumed a param must mark that param `IntoResult` and the aggregate `escapes`). Land the missing negative cell.

## Blocker 2 — confinement `spark_ops` under-propagates (single unordered pass, not a fixpoint)
`fixpoint.rs:236-255` runs confinement once per callable in symbol-table hash order (no topo guarantee), reading callee `spark_ops` from the in-place `summaries` map (`confinement.rs:134-135`). A caller processed before its callee reads the callee's not-yet-computed `spark_ops` (init `false`) and never re-runs → transitive `Crossing` under-reported as `Confined`. Advisory `spark_ops` false-clear → Wave-11 non-atomic RC on a thread-crossing cell → data race / heap corruption. Also **order-dependent** (determinism/cache hazard). Design (§5.3, §13.7 two-deep transitive) requires a fixpoint. Unit test `confinement/tests.rs:111` masks it by pre-setting the callee summary; no driver-level two-callable transitive test exists. **Fix**: run confinement as a worklist fixpoint like the modes stratum; add the transitive driver-level test.

## Blocker 3 (Important) — §13.6(d) let-shadow provenance guard not implemented
`transfer.rs:428-445` provenance is match-only; `(let [x (vec-get g 0)] (let [g …] x))` emits provenance root `g` (the shadowing binding) instead of `None`. Unsound-alias-claim potential for rule-4 last-use, Wave-11 + backend-scope-dependent. **Fix**: implement the symbol-keyed shadow guard (shadowed root ⇒ `None` ⇒ Decision-24 materialize). Land the cell.

## Important 4 — cap-exhaustion publishes partial (too-precise) summaries
`fixpoint.rs:206-211`: on cap `break`, partially-converged summaries publish as-is — an UNSOUND failure mode. **Fix**: on cap exhaustion, reset unconverged entries to conservative ⊤ (all-`Owned`/`Fresh`) before publish. (Cap is defensive; may never trip — but the failure direction must be sound.)

## Suggestion 5 — in-cluster propagation degrades to ⊤ on resolved-call `Symbol` ≠ universe key (mangled mono)
`fixpoint.rs:72-93,222-233`: sound (⊤) but a precision cliff + re-entry miss. Add a test pinning mangled mono-instance in-cluster propagation.

## Operational implication
Gates Wave 11 only, not Wave 9. If S102 pushes through the seam: fix 1/2/3 (+4 hardening) as a mandatory pass BEFORE Wave 11, each with its failing negative cell. If S102 closes short: this rides to S103 as the head of increment-I's second half, fix-then-consume with the mechanisms — the coherent ordering.
