---
number: 0668
target: /design
filed_by: /review
filed_at: 2026-07-19
sprint_filed: 113
refers_to: crates/cranelisp-backend/src/compiler/vec_codegen.rs:190-214 (compile_vec_lit element store); crates/cranelisp-backend/src/compiler/match_codegen.rs (scrutinee temp-dec vs var-arm alias forward); crates/cranelisp-backend/src/compiler/control_flow/let_if.rs:160-172 (the three fn-return patches); crates/cranelisp-backend/src/compiler/apply.rs:88-145 (moded_arg_rc — the rule that already exists at the call seam)
status: open
---

# Binding-indirection consume family: ONE contract gap — syntactic temp-vs-owned classification at non-call consume sites

## Severity

Important (the S113 W5b adjudication family — I-1 residual + probe cells; user ship-vs-carry evidence)

## The seam verdict (one contract, several sites)

Ownership accounting at consume/cleanup sites is decided by LOCAL SYNTAX (is this
node a `Var`? is that expr a "temporary"?) instead of by the value-flow question
"does this consume position receive an independently-owned count?". Every DIRECT
shape is patched: call args (`moded_arg_rc` owned-binding × mode matrix — ctor
fields ride it too), fn-return (`skip_var`/`protect_return_value`/
`return_cow_source` — three ad-hoc patches for one flow), the COW producer
(§13.7 escape gate, W5b). Every INDIRECT flow — a heap value passing THROUGH a
`let` binding or a match var-pattern into any other consumer — falls in the gap,
in two complementary directions:

1. **Missing owned-binding inc at a move-in store**: `compile_vec_lit` stores
   every element raw (vec_codegen.rs:211-214, no inc, temp-transfer assumed); a
   `Var` element is an owned binding whose scope-dec still fires.
2. **Spurious temp-dec of a forwarded alias**: an enclosing match classifies its
   scrutinee "temp" syntactically (non-`Var` expr ⇒ dec after the arm), but a
   match/let RESULT that merely forwards a binding's value is an alias carrying
   no count of its own.

## Evidence (all verified 2026-07-19, debug build, REPL/`--run`, BOTH toggles unless noted; scrub-stable)

| Cell | Shape | on | off |
|---|---|---|---|
| A | `(defn f [v] (let [q (vec-set v 1 99)] [q]))` project | garbage | garbage |
| B | `(defn g [v] (match (match (vec-set v 0 5) [r r]) [q q]))` | garbage | garbage |
| E | `(defn f [] (let [q [7 8 9]] [q]))` — **no COW, no param** | garbage | garbage |
| F | `(defn f [v] (match (match v [r r]) [q q]))` — **no COW** | garbage | garbage |
| G | `(defn f [v] (let [q v] [q]))` — **no COW** | garbage | garbage |
| C | `(defn h [v] (match (vec-set v 1 99) [r r]))` (B-2 direct) | **99 ✓** | **garbage** (copy branch mints a temp scrutinee; match decs it; var-arm forwards the alias; see FIXME 0669) |
| H | `(defn f [v] (match v [r r]))` — bare | 7 ✓ | 7 ✓ (Var scrutinee ⇒ no temp-dec) |
| I-1 | `(let [r v] (fn [] (vec-get r 1)))` capture | garbage (committed RED) | garbage |

Cells E/F/G prove the family is **ownership-independent and pre-COW** — the 0641
COW cells were only its most visible face. CLIF chain for cell A (`CRANELISP_CODEGEN_DUMP`,
mutate path, P = the vec): rc 1 → +1 §13.7 retain → container stores P **uncounted**
→ −1 let-scope-dec of `q` → −1 param consuming dec of `v` → **P freed at `f`'s
return while the returned container holds it**. Cell B: inner scrutinee dec −1,
NO protect between matches (protect fires only at fn-return), outer scrutinee
dec −1 → freed → protect inc on freed box → param dec = double-free.

## Proposed resolution (fix-shape estimate for /sprint's ship-vs-carry)

**Design-iteration (S114-shaped), not small-ruled as a whole.** The correct close
is a /design(backend) consume-position × operand-provenance contract (the §13.5
matrix extended beyond call args to {vec-lit element store, match scrutinee/arm
forward, closure capture, control-flow result}), then serial per-site /dev
change-sets, each with matrix cells — the safety-invariants §3 "close by
mechanism" directive; the three fn-return patches collapsing into the same
contract is the tail. The discriminator is STRUCTURAL (Var-rootedness /
alias-forwarding), analysis-independent — so unlike §13.7's falsified producer
inc, one rule satisfies both toggles by construction.

**One genuinely small sub-fix exists** if a partial in-sprint flip is wanted:
the vec-lit element store compiled through the same consuming discrimination the
call seam uses (Var element ⇒ inc; temp ⇒ transfer; ~15 lines + cells — flips
A/E/G, leak-side-safe, no loop interaction: recur args ride `tail_transfer_skip`,
not vec-lit). The match-forward direction (B/F, C-off) is NOT small — the
alias-forwarding recognizer through arbitrary control flow is exactly what the
contract must define; a one-level recognizer would be instance-patching.

## Sub-fix landing record (S113 W5b, /dev backend — user-approved in-sprint sub-fix)

**LANDED — the vec-lit element store consuming discrimination.** `compile_vec_lit`
(`vec_codegen.rs`) now routes every element store through the SAME
`element_consuming_inc` rule the call seam uses (a heap-typed `Var` element ⇒ one
consuming inc; a temp ⇒ transfer). Structural (Var-rootedness), analysis-
independent — one rule correct in BOTH toggles by construction; leak-side-safe; no
loop interaction (recur args ride `tail_transfer_skip`, not vec-lit).

- **Flips (verified BOTH toggles):** cell **A** `(let [q (vec-set v 1 99)] [q])` → 99;
  cell **E** `(let [q [7 8 9]] [q])` → 7. (The two user-named cells.) `(defn f [v] [v])`
  — the direct owned-param-element form — likewise correct.
- **Cell G** `(defn f [v] (let [q v] [q]))` is **NOT flipped** by this sub-fix and is
  OUT of its scope: G's residual is the **let-binding alias** (`q = v` binds a `Var`
  to a `Var` without counting, so `q` and `v` BOTH scope-dec ⇒ the vec-lit inc pairs
  only one; RC_STATS: allocs=2 deallocs=1, the inner vec freed under the container).
  That is the let-bind consume seam (family direction, not the store) — carries with
  0668 / the S114 contract. The 0668 estimate's "flips A/E/G" over-counted G.
- **Match-forward direction (B/F, C-off) untouched** per the review-REJECTED
  instance-patching bound — 0668's S114 design iteration.
- **Unit cells** (failing-first, `vec_codegen/vec_lit_consume_tests.rs`): a heap `Var`
  element emits exactly one element inc; a temporary element and a NeverHeap `Var`
  element emit none. **E2e cells A/E are unpinned green** — noted for /qa's 0669 pins
  (add committed e2e). Fences hold: l_c3 ×2, golden byte-identical, `vec_lifecycle`
  GREEN; suite 18 REDs, zero unattributed.

**This FIXME stays OPEN for the family** (the let-bind alias for G, the match-forward
recognizer for B/F/C-off, the three fn-return-patch collapse) — the /design(backend)
consume-position × operand-provenance contract, S114.

## Context

S113 W5b review adjudication (dispatched by /sprint; typecheck-review probe cells
+ I-1 residual). Not a W5b regression — the family predates the COW work
entirely. Companion: FIXME 0669 (/qa — family pins incl. the uncovered B-2
toggle-off face).
