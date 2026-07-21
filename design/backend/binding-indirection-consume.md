# The pre-COW binding-indirection consume contract (0668)

**Status:** DESIGN (S114 Phase 3, `/design`(backend) narrow). The S113-named
design-iteration anchor for FIXME 0668 (filed by `/review` S113) — ONE contract
for the consume-position × operand-provenance matrix, converting to serial per-site
`/dev` change-sets. Supersedes the per-site instance-patch bound `/review` REJECTED.

**Governing authority:** `design/arch/safety-invariants.md` §3 ("close by
mechanism") + §4 R14 row; `design/backend/ownership-codegen.md` §13 (the RC-emission
machinery this contract extends — read the §13.7 SUPERSEDED banner FIRST: this
contract is the *separate, orthogonal* family the R14 producer ruling explicitly
does NOT cover). Consumes the `/qa` disposition in `tests/plan/s114-test-plan.md`
§1 (FIXME 0669: the I-1 capture face is re-attributed here) + §2 (the acceptance
rows). Subordinate to `design/backend/backend.md` (§8 indexes this doc).

**Boundary (F4 — binding):** this contract handles the analysis-INDEPENDENT
binding-indirection family (fails under `CRANELISP_NO_OWNERSHIP=1`). It does **NOT**
absorb the B-2 analysis-ON face — the match-var-pattern escape-recording bug is
TYPECHECK work (Track A carrier wave), and the backend gate is correct and cannot
distinguish a wrong-`Some(false)` from the recur-loop `Some(false)` (R14). §4 states
which B-2 face is whose.

---

## 1. Actors and functions first (Principle 21)

The seam verdict (0668): **ownership accounting at consume/cleanup sites is decided
by LOCAL SYNTAX** — "is this node a `Var`? is that expr a temporary?" — instead of
by the value-flow question **"does this consume position receive (or forward) an
independently-owned count?"** Every DIRECT shape is already patched by a bespoke
rule; every INDIRECT flow (a heap value passing THROUGH a `let` binding, a match
var-pattern, or a control-flow result into another consumer) falls in the gap.

**The actors — consume/cleanup positions in today's source** (`crates/cranelisp-backend/`):

- **Call args** — `apply.rs::moded_arg_rc` (the owned-binding × mode matrix; ctor
  fields ride it). DIRECT; patched.
- **Fn-return** — `fn_compiler.rs`: `skip_var` / `protect_return_value` /
  `return_cow_source` — **three ad-hoc patches for ONE flow** (the contract's tail:
  they collapse into it, §5 item 4).
- **Vec-literal element store** — `vec_codegen.rs::compile_vec_lit` (`element_consuming_inc`).
  **LANDED S113 W5b** (the "missing owned-binding inc at a move-in store" direction) —
  a heap `Var` element ⇒ one consuming inc; a temp ⇒ transfer.
- **Match scrutinee dec + var-arm forward** — `match_codegen.rs`
  (`compile_var_pattern_arm`, the scrutinee temp-dec). The "spurious temp-dec of a
  forwarded alias" direction. UNPATCHED.
- **`let`-binding** — `control_flow/let_if.rs`: a `(let [q v] …)` binding a `Var` to
  a `Var` creates an independent scope-dec obligation for `q` while `q` and `v` share
  ONE reference. UNPATCHED.
- **Closure capture** — the capture-store path (`lambda.rs` / `fn_as_value.rs` capture
  emission). Capturing a live-binding alias with no independent count. UNPATCHED —
  and now the re-attributed I-1 face (0669).

**The missing function between them:** ONE
`operand_delivers_owned_count(node) -> bool` (equivalently
`operand_live_binding_root(node) -> Option<Symbol>`) — a **structural**
alias-forwarding classifier over the operand, computed by tracing the operand to its
provenance root through binding-indirection, reading only the scope-stack /
`variables` ("is this a live binding") and never an ownership fact. Every consume
position keys its accounting off this ONE function instead of its local node syntax.

---

## 2. The contract — consume-position × operand-provenance (why it is ONE rule, and why it is NOT the COW escape gate)

**The rule:** at every consume/cleanup position, the RC accounting is decided by
whether the operand delivers (or forwards) an independently-owned count, computed by
tracing the operand's provenance root — NOT by the syntactic shape of the immediate
node.

**Provenance tracing (structural, analysis-independent — the discriminator that
makes ONE rule correct in BOTH toggles by construction):**

| Operand shape | Provenance verdict |
|---|---|
| `Var(x)`, `x` a live scope binding | **alias** of binding `x` (root = `x`) — delivers NO independent count |
| producing op — `[..]` vec-lit, ctor, `vec-set`/`vec-push` result | **owned temporary** — delivers its own count (transfers) |
| `let [.. ] body` | provenance of `body` (a let forwards its body's value); a `body` naming a THIS-let binding that itself aliases an outer root traces to the outer root |
| `match scrut [pat → result]…` | if the selected arm is a var-pattern `[r r]` (or a body forwarding `r`), the match forwards the scrutinee's provenance; else the arm result's own provenance |

**Why this is analysis-independent — the load-bearing contrast with §13.7.** The COW
producer's escape gate (R14 half 2, `ownership-codegen.md` §13.7) reads
`node_escapes` — an ANALYSIS fact, absent under toggle-off, and `/arch` REJECTED
re-deriving it per-consumer (the P7 mirror). This contract's discriminator is
**Var-rootedness / alias-forwarding**, a property of the AST/`MonoExpr` structure
that is IDENTICAL in both toggle states. So one rule satisfies `CRANELISP_NO_OWNERSHIP`
on and off by construction — which is exactly why 0668 is a *separate* family the
R14 ruling's producer-side REJECT does not reach. The two never overlap: the COW
producer decides whether ITS OWN result carries a count (escape); this contract
decides whether a value FORWARDED THROUGH a binding carries one (structure).

**The whole-match approximation (recorded S115, FIXME 0697).** The §2 table's
`match scrut` row keys forwarding on the **selected** arm — a runtime notion. The
as-built implementation is a STATIC whole-match predicate:
`fn_compiler.rs::match_forwards_scrutinee:298` returns true if ANY var-pattern arm
forwards its binder, and R3 emits the scrutinee-dec suppression ONCE in the merge
block (`match_codegen.rs:180-183`). The same any-arm approximation feeds
`operand_live_binding_root`'s Match row (R1/R2 consumers). For a **mixed
constructor+var match** whose var-default arm forwards the scrutinee — a legal,
idiomatic shape, `(match (norm o) [(None) (mk-default)] [x x])` — the suppression
applies on ALL paths, so a run that selects the CTOR arm never decs the genuinely
consumed temp scrutinee: **leak**.

- **Polarity argument (leak-safe — the right direction).** The error is always a
  MISSING dec, never an added one: on the non-forwarding (ctor) path a temp is
  retained, not freed. So the approximation is leak-direction (an at-most-O(depth)
  residue), never an under-count / UAF. Pre-W4 the same mixed shape was
  UAF-direction on the var-arm path (a dec fired on a forwarded value), so the
  whole-match approximation is a STRICT improvement — this record is about fencing
  and bounding it, not reverting it.
- **Mechanism-complete alternative (NAMED, PARKED — "document movable boundaries
  decisively, then park").** Per-arm dec placement: move the temp scrutinee-dec
  OUT of the merge block and INTO the non-forwarding arms before their merge jump,
  so a forwarding arm suppresses and a consuming arm decs — exact per-path
  accounting. It is deferred until a real mixed-arm-leak shape forces it (the
  boundary is movable; today no probed shape exceeds the O(depth) residue bound).
- **Tripwire (coordinated with /qa).** The parked boundary needs a fence: a /qa
  matrix row over the mixed-arm × {ctor-path, var-path} × {toggle-on, toggle-off}
  cells, so a future shape that turns the leak observable trips the both-polarity
  fence. Filed as FIXME `target: /qa` (S115, 0726).

---

## 3. The three coordinated sub-rules (one contract, mapped to the cells)

The one question — "does this consume position receive/pass an independently-owned
count?" — decomposes into three emission rules, all keyed off the §1 classifier:

**Rule R1 — alias-binding recognition (non-owning alias).** A `let` (or match-var)
binding whose value is a live-binding alias (a bare `Var`, or a `Var` forwarded
through control-flow/match-var per §2) is registered as a **NON-OWNING alias** — it
inherits the root's identity for consume purposes and carries **NO independent
scope-dec obligation** (generalises the existing `borrowed_vars` discipline for
match-arm field bindings). This removes the double-scope-dec that frees the shared
box out from under an escaping consumer.

- *Fixes cell **G*** `(let [q v] [q])`: today `q` and `v` BOTH scope-dec while sharing
  one reference (RC_STATS allocs=2 deallocs=1 — the inner vec freed under the returned
  container). Post-R1: `q` is a non-owning alias of `v`; only `v` scope-decs; the
  `[q]` vec-lit consuming inc (R2) is paired by the container's downstream consumer.

**Rule R2 — consume-position inc on live-binding operands (already LANDED for one
position).** At every consume position that STORES/CAPTURES an operand that escapes
the frame — {vec-lit element store (LANDED), closure capture, ctor/container field
store, fn-return} — an operand classified as a live-binding reference (a `Var`, or an
alias registered by R1) gets ONE consuming inc; a genuine owned temporary transfers.
Call args already do this via `moded_arg_rc`.

- *Fixes cell **I-1 (capture face, re-attributed 0669)*** `(let [r v] (fn [] (vec-get r 1)))`:
  `r` is a non-owning alias of `v` (R1); the closure-capture consume incs (R2) so the
  closure holds an independent reference; `v`'s single scope-dec leaves the captured
  reference live. This is structurally cell G's let-bind alias with **closure capture
  as the consume position** instead of the vec-lit store — an already-enumerated
  position in this contract (`s114-test-plan.md` §1).

**Rule R3 — forwarding-suppresses-dec.** At every temp-dec cleanup position — {match
scrutinee-dec, let-value cleanup} — when the value is FORWARDED OUT of the construct
(a var-pattern arm returns the scrutinee; a body forwards the scrutinee's alias) it is
**not a consumed temporary**: suppress the cleanup dec. The value passes through and is
accounted at the OUTER consume position (R2), or at the fn-return protect if it
escapes the function.

- *Fixes cell **F*** `(match (match v [r r]) [q q])` (no COW): the OUTER match's
  scrutinee `(match v [r r])` is a non-`Var` expr, so today it is classified "temp"
  and dec'd after the arm — but its provenance traces (through the inner var-arm) to
  the live binding `v`. R3 suppresses the spurious outer scrutinee-dec; the existing
  fn-return protect handles the escape of `v`.
- *Fixes cell **B*** `(match (match (vec-set v 0 5) [r r]) [q q])` (with COW): same
  outer-match forwarding; the inner COW result is forwarded through both var-arms.
- *Fixes cell **C-off** = B-2 toggle-off* `(match (vec-set v 1 99) [r r])` under
  `CRANELISP_NO_OWNERSHIP=1`: toggle-off (all-Owned, R14) counts everything ⇒ the COW
  copy branch mints a FRESH box as the scrutinee; the var-arm `[r r]` forwards it; the
  match's syntactic scrutinee-temp-dec then frees the fresh box while the arm returns
  it. R3 suppresses the dec; the fresh box is a genuine owned temporary that transfers
  out and is dec'd by its downstream consumer. **Analysis-independent — no escape fact
  consulted** (this is why the toggle-off face is ours, not typecheck's; §4).

The LANDED sub-fix (cells A/E, vec-lit element store) is R2 at one position; R1+R2+R3
generalise the same "provenance not syntax" discriminator to the whole family.

---

## 4. The family matrix + the F4 ownership boundary

From 0668's evidence table (verified 2026-07-19, both toggles unless noted) and the
`/qa` 0669 disposition (`s114-test-plan.md` §1–§2). "Consume position" is the seam
this contract fixes; "root" is the single producer/binding the observation traces to.

| Cell | Shape | Consume position | Rule | Status |
|---|---|---|---|---|
| A | `(let [q (vec-set v 1 99)] [q])` | vec-lit element store | R2 | **LANDED** S113 W5b |
| E | `(let [q [7 8 9]] [q])` | vec-lit element store | R2 | **LANDED** S113 W5b |
| G | `(let [q v] [q])` (no COW) | let-bind alias → vec-lit store | R1+R2 | RED (`let_bind_alias_into_container_neg`) |
| F | `(match (match v [r r]) [q q])` (no COW) | nested-match forward | R3 | RED (`nested_match_forward_alias_neg`) |
| B | `(match (match (vec-set v 0 5) [r r]) [q q])` (COW) | nested-match forward | R3 | NEW ×2 (BI-B-cow), RED |
| C-off | B-2 shape under `CRANELISP_NO_OWNERSHIP=1` | match scrutinee-dec of forwarded alias | R3 | RED (`b2_match_cow_var_pattern_toggle_off_neg`) |
| I-1 | `(let [r v] (fn [] (vec-get r 1)))` capture | closure capture of let-alias | R1+R2 | RED ×2 (re-attributed 0669) |

**The F4 boundary (binding — the contract must NOT cross it):**

- The **B-2 analysis-ON** face `(match (vec-set v 1 99) [r r])` returns 99 correctly
  today (0668 cell C, on=99✓). Its wrong-value residual is the **escape FACT** (typecheck
  records `escapes=Some(false)` for a match-var-pattern transfer that DOES escape). That
  is a TYPECHECK fix in the Track-A carrier wave (F4); its cache-coherence half rides the
  Track-A schema window (F7). **No backend rule in this contract touches the escape fact**,
  and no "distinguish wrong-`Some(false)`" backend workaround is added — R14 says the gate
  is correct.
- The **B-2 toggle-OFF** face (C-off above) is a DIFFERENT mechanism — R3 forwarding
  suppression, analysis-independent. It is ours. The two faces of "B-2" split by the
  toggle; the split is the whole point of the 0669 disposition.
- **Re-attribution rider (0669, MC-E1 protocol):** if the analysis-ON I-1 capture face
  survives this contract's fix while G/F/B flip, a residual typecheck provenance face
  exists and re-attributes to `/dev`(typecheck) `transfer.rs` THEN — with the backend fix
  as the discriminating experiment, not before it. Track A makes NO `transfer.rs`
  capture-provenance change this sprint.

**No schema / types / public-api delta** — codegen-internal RC-emission at
`pub(crate)` seams (the classifier + the three emission rules).

---

## 5. Dev-wave work items (the contract → serial per-site change-sets)

Each item lands with its `§13.5`-style branch/provenance unit matrix (the `/dev` unit
tier `/qa` audits) + its `s114-test-plan.md` §2 acceptance cell(s), failing-first. The
`/dev` root-cause obligation (the §13.3 "twice-burned" discipline) holds: confirm the
imbalance's seam against `CRANELISP_RC_TRACE`/`RC_STATS`/`CODEGEN_DUMP` (+
`MALLOC_PERTURB_`, asserting the RESULT not balance) BEFORE landing each.

| Item | Work | Flips | Acceptance |
|---|---|---|---|
| **W-B0 (LANDED)** | vec-lit element store consuming discrimination (R2 at one position) | A, E | landed S113 W5b; unit `vec_lit_consume_tests` |
| **W-B1** | the ONE shared `operand_delivers_owned_count` / `operand_live_binding_root` classifier (structural provenance trace); no behaviour change on its own — the foundation the rest key off | — | unit cells: Var-root, producing-op temp, let-forward, match-var-forward, nested; a NeverHeap Var ⇒ no inc |
| **W-B2** | **R1** alias-binding recognition — a `Var`-aliasing `let`/match-var binding registers non-owning (no scope-dec obligation) | G (with W-B3's consume inc) | BI-G; unit: alias binding emits no scope-dec; RC balanced |
| **W-B3** | **R2** extend the LANDED consume-inc to {closure capture, ctor field store} via the W-B1 classifier | I-1 ×2 (capture) | BI-I1 ×2; unit: capture of a live-binding alias incs once; locus line updated to `class=uaf locus=…backend let-bind-alias / closure-capture consume seam (FIXME 0668)` |
| **W-B4** | **R3** forwarding-suppresses-dec at the match scrutinee-dec seam (`compile_var_pattern_arm`) | F, B ×2, C-off | BI-F, BI-B-cow ×2, BI-C-off; unit: forwarded-alias scrutinee ⇒ no dec; a genuine-temp scrutinee ⇒ dec (cell H twin stays GREEN) |
| **W-B5 (tail)** | collapse the three fn-return patches (`skip_var`/`protect_return_value`/`return_cow_source`) onto the same provenance contract — the "three ad-hoc patches for one flow" 0668 named | — (hygiene; regression-fenced) | golden byte-identical-off; `l_c3` ×2, `vec_lifecycle`, A/E ×2 HOLD; no new RED |

**Must-hold fences through every item** (`s114-test-plan.md` §2): A/E ×2, cell-H
bare-match, `ownership_reuse::l_c3_*` ×2 (escape-gated reuse — untouched by this
contract), the CLIF golden lane, `vec_lifecycle`, the B-2 analysis-ON twins
(`match_scrutinee_cow_var_pattern_*` stay GREEN). W-B1..B4 order matters (the classifier
precedes its consumers); W-B4 and the carrier consumer-flip both touch `match_codegen.rs`
— serialize them (shared-tree race, root `CLAUDE.md` §Testing), but there is NO semantic
dependency (§7).

---

## 6. Sibling Track-B leak-direction REDs — F-R1 and MS-P8 (SEPARATE mechanisms)

These are Track-B backend REDs but are **NOT** the binding-indirection UAF family — they
are the leak (over-retain) direction, distinct mechanisms. Recorded here so `/dev`(backend)
has ONE Track-B map, but each names the root-cause discriminator FIRST because the seam
attribution is genuinely unsettled (and, per the evidence below, may fall OUTSIDE the
backend surface). Both are BOTH-POLARITY fenced (`s114-test-plan.md` §2): the fix must make
`allocs==deallocs` EXACTLY — it must not over-correct into an under-count (the S110-8/S111-2
inversion lesson).

### 6.1 F-R1 — entry-`main` IO-teardown fixed-residual leak (×2)

**Repro** (`adt_drop_glue_underkey.rs::entry_main_heap_let_teardown_balances_r2` + the
`ownership_reuse` R-3 residual family): `(defn main [] (let [s "hi"] (Pure 9)))` → 2 allocs /
1 free. The `s` string box IS freed; the **final IO/result box** (the `(Pure 9)` box) leaks.
Ownership-independent (leaks toggle-off), scale-INVARIANT (the delta stays 1 as the heap-let
count grows; the `ownership_reuse` CHAIN_SRC face is delta-4 invariant across N=8/64/256) —
i.e. a SINGLE fixed over-retention at the result-consumption boundary, not a per-value
accounting bug.

**Seam evidence (S114 P3, `/design` survey — this is why attribution is unsettled).** The IO
trampoline and the result-tree teardown live in **`cranelisp-intrinsics`**, not backend:
`panic.rs::cranelisp_run_program` (`:259`) calls `main`, then `io::drive_io(main_result)`
(`:289`) to force the payload and `drop::consume_io_tree(main_result)` (`:291`, "Decision 24:
release the caller's tree, non-consuming driver"). So the single dec that should free the root
`Pure` box is `consume_io_tree`'s job. Two candidate roots, ONE discriminator:

- **(a) Backend over-inc at the entry-`main` return.** `main` has a heap cleanup target (`s`),
  so `protect_return_value` (`rc_emission.rs`) incs the returned `(Pure 9)` box to rc=2 —
  exactly the §13.3 G2/item-26 class (a protect over-inc of a **fresh** return value scope
  cleanup can never free). The trampoline's single `consume_io_tree` dec brings it to rc=1 →
  leak 1. Unlike the general G2/item-26 case (which needs B2 callee summaries), `main` is a
  known nullary top-level entry with a SINGLE consumer (the trampoline), so the fix is
  local: **suppress the return-protect on `main`'s IO result** (or pair it with a second
  teardown dec). Backend surface — this doc's family neighbour.
- **(b) Intrinsics `consume_io_tree` root-leaf non-free.** If `main` returns the `Pure` box at
  rc=1 and `consume_io_tree` walks the tree's CHILDREN but never dec's the root `Pure` LEAF's
  own box, the leak is in `cranelisp-intrinsics::drop` — the **Runtime surface, OUT of
  backend** (re-attributes to `/dev`(runtime/intrinsics)).

**Discriminator (the `/dev` obligation, before any fix):** `CRANELISP_RC_TRACE=1` on the
2-line repro and read the `Pure` box's inc/dec history. rc=2-at-return (a `protect` inc) ⇒
**(a) backend**; rc=1-at-return with no `consume_io_tree` dec of the leaf ⇒ **(b) intrinsics**.
The characterization (single fixed residual at the result boundary) fits either. **Attribution
is filed to `/qa` (FIXME below) so Phase-4 wave assignment does not pre-commit the leak to
backend before this discriminator runs** — the `s114-test-plan.md` §2 owner line
("backend main-epilogue / int IO-trampoline result-dec seam") predates the intrinsics-seam
evidence.

### 6.2 MS-P8 — `conj`/`assoc` persistent-op leak (×2)

**Repro** (`ms_p8_conj_leak.rs`): a `go` loop `(go (add-i64 n -1) (conj v n))` leaks 1 Vec per
iteration (`allocs=22 / deallocs=2` at 20 iterations). Specific to the **stdlib persistent
verbs** `conj`/`assoc` (`stdlib/collections/vec.cl:35,39`) — which route through the COW
copy path — NOT the primitive `vec-push` (which reuses in-place, mutate branch, no new box
so nothing to leak). `class=rc-miscount` leak polarity, non-corrupting (QUARANTINE+SCRUB
clean ⇒ no UAF).

**Mechanism (the copy branch exposes it).** Each `(conj v n)` copies (rc≥2 because both the
loop-param slot and `conj`'s consumed arg reference `v`) → a FRESH box; the OLD `v` is
superseded. In the tail self-call, the loop-param slot is overwritten with the new box. The
old box's reference must be released — and is not (1 leak/iter). Candidate roots, ONE
discriminator:

- **(a) Loop-param overwrite dec (backend TCO).** A tail self-call overwrites a heap-typed
  loop param; the OLD value's reference must be dec'd before the slot is overwritten. On the
  persistent/COW path (`conj` copies, leaving the old `v` for the caller to release) the old
  param may never be released — the PARAM sibling of the §13.3 B3.1a dead-block let-scope
  leak (which fixed `let`-bindings via `flush_let_scopes_before_tail_jump` but the PARAM
  slot is a distinct seam). Backend surface.
- **(b) COW copy-branch source release (backend polarity).** `§13.3 Ruling 2`:
  `release_consumed_source` decs the copy source iff `Owned`. If `conj`'s vec arg is
  classified `Borrowed`, the copy branch releases nothing and relies on a caller scope-dec
  that (per (a)) never fires. Backend surface — a wrong source polarity at the `conj` call.
- **(c) Intrinsics copy-fn.** `vec-set-copy`/`vec-push-copy` (`cranelisp-intrinsics/src/vec_runtime.rs`)
  retain-element-inc the copied elements; if the SOURCE struct box itself is not accounted at
  the copy, the leak is in `cranelisp-intrinsics` — Runtime surface, OUT of backend.

**Discriminator (the `/dev` obligation):** `CRANELISP_RC_TRACE=1` on `CONJ_LOOP`, identify the
leaked box (the superseded old `v` each iteration) and the site where its dec should fire. A
missing dec at the tail-jump slot overwrite ⇒ (a); a copy-branch source-polarity miss ⇒ (b);
an unaccounted source struct inside the copy fn ⇒ (c). The `INT_LOOP` control (primitive
add, no vec) balances — so the leak is specific to the heap-vec persistent path, confirming
it is NOT the generic TCO machinery (else the int loop would leak too).

**Both F-R1 and MS-P8: the fix shape is contingent on the discriminator.** The design records
the candidate seams and the ONE experiment that decides — it does not pre-commit, consistent
with `memory/feedback_verify_fix_not_symptom_absence` and the §13.3 twice-burned discipline.
If either discriminator lands the root in `cranelisp-intrinsics`, it re-attributes to the
Runtime surface and leaves this contract's scope.

---

## 7. Sequencing (Phase 4 input)

**Independent of the Track-A carrier flip.** This contract is RC-emission; the carrier
(`VarRef`/`ApplyRef`) is resolution. No semantic dependency either way. The ONLY coupling is
FILE-level: W-B4 (R3 in `match_codegen.rs`) and the carrier consumer-flip (exhaustive
`VarRef`/`ApplyRef` matches, also in `match_codegen.rs`, `backend.md` §2.7.2) touch the same
file — serialize the two `/dev` change-sets (shared-tree race), no wave-gate ordering.

**The B-2 split (F4/F7 — binding on Phase 4):**
- B-2 **toggle-OFF** face (BI-C-off) flips with W-B4 (R3) — this contract, this sprint.
- B-2 **analysis-ON** escape-fact correction is TYPECHECK (Track A carrier wave); its
  **cache-coherence half** (stale persisted `Some(false)`) rides the Track-A schema window
  (21→22, ONE bump, F7) — NOT a second invalidation event here. This contract adds no schema
  bump (§4).

**Within the family:** W-B1 (classifier) precedes W-B2/B3/B4 (its consumers); W-B5 (fn-return
patch collapse) is the hygiene tail after the family flips green. W-B0 is landed.

**F-R1 / MS-P8:** wave-UNASSIGNED until their §6 discriminators run — the evidence decides
backend-vs-intrinsics before Phase-4 places them. `/qa` adjudicates from the FIXME.

**MS-P7** is not this contract's (evidence-gated `--link` divergence, `s114-test-plan.md`
§3.6); named here only to exclude it.

---

## 8. Testability + acceptance

The authoritative acceptance rows are `tests/plan/s114-test-plan.md` §2 (the family matrix)
— this doc does not restate them. The `/dev` unit tier is the per-item branch/provenance
matrices (§5) at seam × class grain (`§13.5` template, Principle 23). The twin discipline is
binding: every RED names its GREEN twin in-file (cell H for the match rows; cell E for the
alias rows). The `[oracle]` graduation (family through `assert_safety_matrix` where the lane
supports the toggle axis) is `/qa`/`/testing`'s; this contract's cells are toggle-pair cells
until then.
