# Sprint 111: vec-assoc COW ownership root + backend audit-debt drain + quasiquote normative

Status: PHASE 2 ARCHITECTURE REVIEW (scope user-approved 2026-07-17)
Audit: cranelisp-frontend (rotation — longest since assessment, s87; /sprint sets final target at Phase 4)

## Phase-1 decisions (user-approved 2026-07-17)

1. **Breadth: BROAD** — centrepiece + full backend audit drain + quasiquote + Principle-24 sweep + adjacent carries. Decomposed into waves.
2. **0613 quasiquote: ruled (A) LEGAL EVERYWHERE.** Quote/quasiquote desugar wherever an expression is legal. Sole owner is `cranelisp-frontend` (a wiring fix, no typecheck/backend involvement, no new special form — see §3). Routes to `/dev`(frontend) + one-line `/arch` seam note + `/testing` matrix. 0614 becomes a `/stdlib` no-op (derive.cl helpers compile once the wiring lands); 0615 rides.
3. **4th-audit backend items: SHIP ALL this sprint** (dup `build_isa`, dispatch funnels, drop-glue, GOT exhaustion) — no 3rd deferral.

## Scope

**Breadth: BROAD (user-approved).** One `/arch`-ruled centrepiece with 4 failing guards to
flip, a Phase-1-mandated double audit disposition whose must-ship subset is past the
2× deferral threshold, one language-normative gate, and a well-defined Principle-24
verification lane. Coherent because the centrepiece and the backend audit both live on
the ownership/keyed-seam frontier the last two sprints built.

### 1. CENTREPIECE — vec-assoc COW ownership root (0623 + the 4 RED siblings + 0621 rider) — LEAD

The largest live technical debt with a **ruled design and the most failing guards**.
S110 `/arch` ruled the 3-layer ownership root: `ResultMode::MayAliasOf` + truthful COW
facts + prelude-fallback-aware environments, **cache schema 19 → 20**, delivered as ONE
coordinated change-set. The four RED guards are the vec-assoc COW siblings
(let-wrapped + match-arm × REPL/`--link`); 0623 is the body-shape × branch × face
coverage matrix `/qa` must author around it. **0621 callees-alias rides the schema-20
bump** (evidence-gated: the session-transaction reverse index it would bite is not yet
live — confirm before pulling). Flips 4 of the 7 RED carries green.

Crates: `cranelisp-typecheck` (ownership inference), `cranelisp-backend` (COW codegen),
`cranelisp-types` (schema 20 + `ResultMode` variant). `/arch` interface approval required.

### 2. PHASE-1 OBLIGATION — dispose BOTH backend audits (s107 + s110)

`/audit` caught that **`audits/cranelisp-backend-s107.md` §4 was never disposed** (the
protocol's inaugural application — a process lapse). Four of its seven recommendations
have now hit their **4th consecutive audit**. S111 Phase 1 MUST:
- Retroactively append the s107 §4 disposition trail (each R1–R7: accepted → FIXME, or
  declined + rationale — declining is legitimate; lapsing is not).
- Dispose backend-s110 R1–R8.

**Must-ship subset (past 2× threshold or release-phase-critical):**
- **s110 R7 / s107 R7 — GOT slot exhaustion → diagnosed error (currently release-mode UB).**
  3rd consecutive naming; we are IN Phase H (the release phase); `allocate_got_slot`
  unchecked monotone, `debug_assert!` only, no boundary test. Seam is `cranelisp-types` → `/arch`.
- **s110 R2 — pin the three hard-miss `CodegenError` families** (the Principle-24 seam's
  negative side; `backend-keyed-consumer.md §9` names them as pinned acceptance; zero test
  hits today). Cheap, high-value regression guard.
- **s110 R4 / s107 R1+R2+R3 — hygiene batch** (4th-audit dup `build_isa`, Wave-2b shims,
  `compile_defn` disposition, `module_aliases` drop). One change-set.
- **s110 R5 dispatch-funnel splits** (4th-audit: `compile_resolved_call` ~325 ln,
  `compile_to_module_impl` ~395 ln — both grew since s107).

### 3. NORMATIVE — 0613 quasiquote-not-desugared: RULED (A) legal everywhere

Quote/quasiquote die as parse errors in every non-`defmacro` position (`(defn f [] '(1 2))`
fails; the same template in a `defmacro` clause works). **User ruled (A):** quote/quasiquote
are legal wherever an expression is legal.

**Architecture (traced 2026-07-17, confirms sole frontend ownership):** quasiquote is NOT a
special form — the reader turns `` `form `` into `Sexp::List[Symbol("quasiquote"), form]`, and
`quasiquote.rs::expand_quasiquotes` is a pure `Sexp→Sexp` structural rewrite into
`macros/Sexp*` constructor-application lists. It is *eliminated before* `build_form`; the
`ast_builder.rs:1160+` rejection is the backstop invariant (a surviving quasiquote symbol = bug).
Typecheck/backend never see it — after desugaring it is ordinary constructor application yielding
`Sexp`, type-identical to the hand-written raw-ctor form (which already compiles in `defn` bodies).
The transform is position-independent; only the *wiring* is partial (sole prod caller
`macro_clause.rs:67`; the universal AST chokepoint `build_forms`/`build_form` never calls it,
though `lib.rs:48` claims it does).

**Fix (single-codepath lever):** fold `expand_quasiquotes` into `build_forms` so every form is
desugared before dispatch; `macro_clause.rs`'s call becomes idempotent; backstop stays. → `/dev`
(`cranelisp-frontend`) + one-line `/arch` seam note. `/testing` pins the form × position × mode
matrix. **0614 collapses to a `/stdlib` no-op** (derive.cl's plain-`defn` templates compile once
the wiring lands — no raw-ctor rewrite needed); **0615 rides**.

### 4. Principle-24 enforcement sweep — compiler-wide identity-scan classification

Ratified at S110 close as a well-defined verification task: classify every unindexed
iteration compiler-wide as enumeration (legit, carve-out 1) or identity-scan (defect).
Acid test: *does the answer depend on incidental order (hash/insertion/directory)?*
Read-only verification lane → `/qa` plan + `/audit` (rides the frontend rotation).

### 5. Adjacent carries (breadth-dependent — decompose into waves, not dropped for size)

- **0604 index-race** — `/qa` re-attributed to foreground (proven, not the index feed); needs the fix.
- **0590 R1/I2** — 0349 3rd instance, pre-existing safe-direction wrong-reject → `cranelisp-typecheck`.
- **0595 structural hardening of rigid-unify invariants** → `cranelisp-typecheck`.
- **Phase-6 gap FIXMEs (S110-filed):** 0628 (HKT-on-primitive bare-convar leaks codegen → `/design` tc),
  0630 (spec §5.1.2 bare-`:Vec` example uncompilable → `/spec`), 0631 (return-poly `:Type` remedy → `/docs`).
- **0589** qualified-lowercase annotation `TypeVar`-routing leg → `/dev` (frontend).
- **0591** §L annotation-position parse-gap map → `/qa`.
- **0553** "instantiate symbol at these types" SET-capture (T1 reload cure) → `/typecheck` — LARGE design; likely its own sprint.

### Long-parked user-proxy carries (2×+ deferred — §2.4 disposition needed)
- **0050** list/seq pretty-printer (deferred S64, `target_sprint: TBD`, blocked on display-protocol design) → /int (now /dev int).
- **0052** docs learn-system REPL feature (user-deferred S107) → /repl.
- **0463** network-poll-shape example (open since S99) → /examples.

### Out of scope (proposed deferrals — rationale)
- 0553 SET-capture: large standalone design; carry unless user wants it as a second centrepiece.
- 0050: still blocked on non-existent display-protocol design — 3rd-deferral sign-off or leave parked.

## FIXME debt

Open at Phase 1 (19): 0050, 0052, 0463, 0553, 0577, 0589, 0590, 0591, 0595, 0605,
0613, 0614, 0615, 0621, 0623, 0628, 0630, 0631, 0604. Disposition above.
Backend audit recommendations (s107 R1–R7, s110 R1–R8) become FIXMEs on acceptance.

## Architecture review (Phase 2) — `/arch`, 2026-07-17

**Verdict: SIGNED OFF with two scope corrections and one pinned matrix obligation.**
The BROAD scope is coherent; the centrepiece, the audit drain, and the quasiquote
fix live on three nearly-disjoint seams, so breadth here is decomposition-friendly,
not entangled. The corrections: (1) 0613 is NOT sole-frontend — int's macro
expander needs a quote shield in the same logical wave (§3 below); (2) the 0050
parking rationale is stale — the display-protocol design EXISTS (S106, both forks
user-settled), so the honest disposition is "defer for size / schedule the
implementation sprint", not "blocked on non-existent design". No `cranelisp-types`
edit lands at Phase 2 — both pinned types diffs (§2) are same-change-set-coupled
to cascades (schema bump; caller sweep) and land in their implementing waves per
the baseline-diff discipline.

### 1. Coherence of the centrepiece + binding ordering constraints

**The schema-20 change-set is genuinely ONE coordinated change-set** — the §3.7
ruling (`design/arch/ownership-inference.md`) stands as scoped: `cranelisp-types`
(`ResultMode::MayAliasOf(usize)`) + `cranelisp-primitives` (`ownership_facts.rs`
truthful COW declarations) + `cranelisp-typecheck` (prelude-fallback-aware
ownership envs + transfer-join arms) + backend rustdoc corrections (B3.2
falsity), with `CACHE_SCHEMA_VERSION` 19→20 in `cache/mod.rs`. Splitting any
layer out re-creates the false-`Fresh` state the ruling exists to kill: a2
without a3 is dead code; a1 without a2 has no producer.

**0621 rides the schema-20 bump — confirmed, and tightened: same CHANGE-SET, not
merely same sprint.** The `user_fn_refs.insert(span, resolved.fq)` →
`storage_fq()` flip is a meaning change to persisted `.meta.json`; the schema
constant flips exactly once, so both meaning changes must be inside the one
commit window that bumps it (a cache written between two separate bumps would
carry schema-20 with alias `callees`). It is technically separable only at the
cost of a second bump — strictly worse. The rider is typecheck-side, small,
with its own unit pins (renamed-import + bare-accessor `callees`); verify at
landing that `extract_call_graph_edges`' ResolvedCall channel is already
storage-keyed (post-W0.1b it is, per 0621).

**Wave-order constraints (binding on Phase 4):**

1. **Byte-identical backend work BEFORE the emission-affecting ownership wave.**
   The audit-drain items R4 (hygiene batch) + R5 (funnel splits) carry a
   CLIF-byte-identity gate; the ownership change-set is emission-affecting by
   design with a scoped+attributed re-baseline (S102 §6.2). Interleaving them
   muddies golden attribution. Order: R2 negatives (pin the keyed-miss families
   first — they guard everything after) → R4/R5 byte-identical → the schema-20
   ownership wave (+0621) with its re-baseline as the wave's last act.
2. **Quasiquote: int quote-shield lands ≤ the frontend fold** (§3). Shield-only
   is inert-safe (quote still dies at `build_form`); fold-without-shield opens a
   NEW wrong-behaviour surface (macro expansion corrupting quoted data).
3. **GOT R7 is schema-independent** (no serde change — `next_got_slot`'s shape
   is untouched; only allocation becomes fallible). Any slot; suggest early,
   riding the backend-drain track.
4. **Principle-24 sweep and the audit rotation are read-only** — no ordering
   constraint except that the frontend assessment should run after the
   quasiquote fix lands (Phase-6 timing, the S110 post-W3 precedent), so the
   boundary lens sees the end-state.
5. The typecheck adjacent carries (0590 R1/I2, 0595, 0628-design) ride the
   typecheck track serially; 0595's item (1) is two call edits and can ride any
   typecheck wave opportunistically, per its own filing.

### 2. Public-API / cross-crate impact table

| Change | Crate(s) | Surface | `cargo-public-api` impact | Approval |
|---|---|---|---|---|
| `ResultMode::MayAliasOf(usize)` | `cranelisp-types` | public enum variant | types `public-api.txt` +1 line; schema 19→20; `interfaces.md` §"Ownership-inference carriers" + §3.3 sketch cascade — all one change-set | **APPROVED**, diff pinned by §3.7; `/arch` authors at Phase 3/implementing wave |
| Truthful COW facts (`vec-set`/`vec-push` → `MayAliasOf(0)`) | `cranelisp-primitives` | internal (fact-table rows + rustdoc §9.3 + test pins) | none | routed `/dev` (backend-mode primitives) |
| Prelude-hop ownership envs; transfer-join `MayAliasOf` arm | `cranelisp-typecheck` | internal (`ownership/fixpoint.rs`, `confinement.rs`, `transfer.rs`) | none | — |
| 0621 `callees` → `storage_fq()` | `cranelisp-typecheck` | internal; **persisted-meaning change** | none (schema rides 20) | — |
| GOT exhaustion (R7): `allocate_got_slot` → fallible | `cranelisp-types` (seam) + caller sweep | `pub fn allocate_got_slot(&mut self) -> usize` becomes `Result<usize, _>` (+ a small types-hosted exhaustion error, mapped into `CheckError`/`CodegenError` at callers) | types `public-api.txt` signature change; typecheck/backend baselines likely unchanged (callers internal) | **APPROVED in shape**; `/arch` pins the exact diff at Phase 3. Callers enumerated: 9 production sites in typecheck (`adt.rs` ×2, `impl_check.rs:667`, `program/body.rs` ×2, `program/finalize.rs` ×2, `monomorphise.rs:611`, `builtins.rs:694` — bootstrap site uses `unreachable!` per convention, a fresh table cannot exhaust) + backend `extern_call.rs:151`. Boundary unit test 1023→1024 in `cranelisp-types/src/module/tests.rs` + one session-surfaced e2e-or-unit at a caller |
| R4 hygiene batch: `module_aliases` off `CompileContext` | `cranelisp-backend` + int call sites | `pub compile_to_module` signature moves | backend `public-api.txt` regen (int is a binary — e2e gate, no baseline) | **APPROVED** — the field is threaded-but-UNREAD since W3; a 5th audit carrying it would be a Principle-8 failure |
| R2 hard-miss `CodegenError` negatives | tests only (backend unit tier per audit R2) | none | none | — |
| R5 funnel splits | `cranelisp-backend` internal | none (byte-identity gate) | none | — |
| Quasiquote fold into `build_form`/`build_forms` | `cranelisp-frontend` | **zero public-API diff** — `build_form`/`build_forms` signatures unchanged; `expand_quasiquotes` stays `pub` (the `macro_clause.rs:67` caller becomes idempotent — the transform is a fixpoint, no quasiquote symbols survive one pass); `ast_builder.rs:1160+` rejection stays as backstop | none; `lib.rs:48`'s currently-false claim ("desugaring runs before `build_form`") becomes TRUE — cite the currency fix in the change-set | **APPROVED** |
| Int expander quote shield (§3) | `src/expander.rs` (binary) | internal | none (binary conformance gate is the e2e suite) | routed `/dev` (int) |

**One structural note for the types diff:** `ResultMode` (and `Mode`/`ParamFlow`)
deliberately carries **no `#[non_exhaustive]`** — for ABI-bearing mode enums this
is the safety feature, not a policy lapse: adding `MayAliasOf` forces every
exhaustive consumer match in typecheck to be revisited at compile time
(Principle 18's structural completeness), whereas `#[non_exhaustive]` would
compel exactly the `_ =>` wildcard arms that hide a missed variant. Phase 3
records this exception in `ownership.rs` rustdoc + the types `CLAUDE.md`
exception list. The change-set review greps for `_ =>`/`== Fresh` over
`ResultMode`: the two known binaries (`return_is_fresh_by_summary`,
`is_abi_conservative`) are each safe-direction for the new variant (protect
kept; non-conservative classification) — verify no third.

### 3. 0613 correction — the quasiquote wave is frontend + a small int leg

The Phase-1 trace ("sole owner `cranelisp-frontend`, a wiring fix") is right
about the desugar mechanism and the fold point, but missed one seam that becomes
live the moment quote is legal everywhere: **int's `expand_sexp_recursive` /
`expand_scoped` (`src/expander.rs:715–829`) recurses into ALL sub-lists with no
quote/quasiquote handling** (verified: zero `quote` hits in the file; the only
verbatim shields are binding forms + the `defmacro` name). The Pass-1 macro
expansion runs BEFORE `build_forms`, i.e. before the fold's desugar point — so
post-fold, a macro-call-shaped list inside quoted data is macro-expanded before
the desugar ever sees it: `(defn f [] '(m x))` with `m` a registered macro would
have its quoted LITERAL rewritten to `m`'s expansion — data corruption, silent.
Today this path is masked only because the quote dies at `build_form` first;
the fix unmasks it.

**Ruling (the seam note the scope asked for):** keep the fold at
`build_form`/`build_forms` (the single-codepath lever, and it keeps macro
ARGUMENTS raw — a macro receives the `(quote …)`/`(quasiquote …)` sexp the user
wrote, which is the conservative semantics; desugar-before-expansion would
change macro-arg representation observably). In the SAME logical wave,
`expand_scoped` gains the quote shield: hold `quote` subtrees fully verbatim;
within `quasiquote`, descend ONLY into `unquote`/`unquote-splicing` bodies
(those are ordinary expression positions where macro calls SHOULD expand);
track quasiquote nesting depth so nested quasiquotes stay shielded. This
manifests at Phase 3 as: frontend rustdoc (the fold, the idempotence contract,
the backstop) + a BC §1/§6 sentence each (frontend desugars; int's expander is
quote-blind by shield, not by accident). `/testing`'s 0613 matrix gains the
interaction rows: {macro-call shape inside quote / inside quasiquote outside
unquote / under unquote / under unquote-splicing} × {defn body, top level} —
the first two must NOT expand, the last two MUST.

Consequence for dispatch: two surfaces, one logical wave — `/dev` (frontend,
the fold) + `/dev` (int, the ~15-line shield), shield lands before or with the
fold per ordering constraint 2. 0614 stays a `/stdlib` no-op; 0615 rides.

### 4. Principle-24 enforcement sweep — scoped

**What it checks.** Every unindexed iteration in the pipeline (the grep classes:
`symbol_tables.iter()`, `.iter()`/`.values()`/`for` over module maps, DashMap
walks, directory walks feeding resolution) is classified by the Principle-24
acid test — *does the result flow into a compile-necessary identity, and does
the answer depend on incidental order?* — into: **enumeration** (carve-out 1;
discipline verified: complete set consumed, tie = ambiguity error, never
first-match) or **identity-scan** (defect → failing test or FIXME naming the
owner). `/search` sites are carve-out 2 by name.

**Which crates.** `cranelisp-typecheck`, `src/` (int), `cranelisp-frontend` —
in that priority order (typecheck has the largest iteration surface; int's
eval/dispatch/expander paths matter, its display/introspection paths are
non-identity by D1). **Backend is DONE** — the S110 audit §2.1 already classified
its four surviving `symbol_tables.iter()` walks as legit enumerations (cite,
don't redo). `cranelisp-types/resolve.rs` is the sanctioned chain itself
(re-read only if a pattern hit lands there). Primitives/intrinsics/platform
have no resolution role — a single grep pass confirms zero hits and closes them.

**Shape: read-only, no design artefact.** The principle file IS the criterion;
no new mechanism is designed. Deliverable = a classification register (site →
verdict → grounds), manifested in the S111 audit artefact + `/qa`'s plan rows;
any identity-scan found becomes a failing test (defect rule) or FIXME. Division
of labour per the scope, sharpened: `/qa` authors the pattern battery +
classification criteria as plan rows (small — the acid test and carve-outs
transcribe from `principles/24-resolve-once.md`) and owns the compiler-wide
register + attribution of findings; `/audit`'s frontend-rotation assessment
carries the frontend leg in depth (its §2.1-style verification section). This
keeps `/audit`'s one-context charter clean while the sweep stays compiler-wide.
The `jit.rs:117` last-write-wins observation from the S110 audit (platform
names globally unique today) is a pre-seeded register row: enumeration whose
tie-discipline is convention-only — the sweep decides whether it needs a
structural tie-error.

### 5. Principle 8 + the carrier-completeness matrix obligation — FLAGGED UP FRONT

**P8 review: no interim implementations in scope.** The one explicitly-interim
artifact is the re-scoped `return_cow_source` recognizer — acceptable because
it is named, its deletion trigger is named (walk-emitted per-site facts), and
its residual is fence-pinned (0623 item 2). Watch item: R4's
`module_aliases` drop must actually land this time (see §2).

**Yes — the schema-20 change carries the analogous matrix obligation.** The
S110 lesson ("a new cross-crate carrier needs its axis×path matrix enumerated
up front") generalizes to a carrier whose SEMANTICS are extended: enumerate the
axes before `/dev` writes a line. Four axes, owners assigned:

1. **Reachability axis (the a3 leg):** fact-lookup sites × reach paths. Sites
   (from §3.7, to be re-verified complete by `/design` typecheck):
   `ClusterEnv::{summary_of, terminal_kind}` (`ownership/fixpoint.rs:72–93`),
   the `UniqClusterEnv` twins (`:388–415`), confinement's read
   (`confinement.rs:162`) — five, × {same-module def, explicit-import chain,
   prelude fallback}. Structural rule (Principle 7, binding): ONE shared
   prelude-hop helper routed through the existing scope-resolve machinery —
   never five hand-rolled hops; `/design` confirms no sixth site by grepping
   `resolve_terminal_entry_and_home`/`probe_module_entry_owned` under
   `ownership/`.
2. **Variant axis:** every `ResultMode` consumer match — structurally forced by
   the enum's exhaustiveness (§2 note); review greps for wildcard/binary escapes.
3. **Producer axis:** `origin_to_result_mode` publish arms (`transfer.rs:240–252`
   — `MayParam{projection:false}` → `MayAliasOf`, hard `AliasOf`/`ProjectionOf`
   reserved for unconditional claims) AND a completeness sweep of the WHOLE
   `ownership_facts.rs` table for other convention-deviating primitives (any
   COW-shaped emission beyond `vec-set`/`vec-push` — the ask is "no other
   `Borrowed`-emission primitive declares `Fresh`", not just the two named
   rows). The `cranelisp-primitives/CLAUDE.md` declared-facts contract sentence
   (§3.7) is the durable form.
4. **Behavioural axis:** 0623's body-shape × branch × face matrix + the two
   fences — already filed to `/qa`; actioned at Phase 3.

### 6. 0553 SET-capture — DEFER, with a named (now-checkable) trigger

Defer out of S111. Grounds, in order of weight: (i) its natural co-landing
context is the session-transaction machinery going LIVE (the reverse index +
dependent recompilation), and S111 itself creates that trigger's precondition —
0621's `callees` fix is a hard prerequisite for the reverse index (0621 §Impact:
"MUST NOT go live while `callees` can carry alias edges"). Sequencing:
S111 lands 0621 → the session-transaction activation sprint is unblocked →
0553 co-lands there (or immediately after) as its own centrepiece, where the
typecheck+backend "instantiate at types" pair shares that sprint's open seams.
(ii) Neither of 0553's two limitations is biting today — the S106 reachability
argument holds and no defect traces to it. (iii) S111 is already BROAD with a
schema window + a double audit drain; a second large design centrepiece
over-fills it. This is a trigger-gated deferral (the legitimate kind), not a
size-habit one — and unlike last sprint, the trigger is now concrete and
checkable at any Phase 1: "is the session-transaction machinery scheduled to go
live?"

**Related correction for the parked carries:** 0050's out-of-scope rationale
("blocked on non-existent display-protocol design") is stale — 
`design/arch/display-protocol.md` is DESIGNED (S106 Phase 3, both §10 forks
user-settled 2026-07-10) and its own text calls the §1.5 promotion "an ordinary
implementation sprint, no user gate". The honest S111 disposition is
**defer-for-size with the implementation sprint named as the successor slot**
(S112 candidate), not blocked-on-design. `/sprint` updates the rationale line.

### 7. Audit rotation — CONFIRMED: `cranelisp-frontend`

Longest since assessment (s87) AND the sprint's frontend-touching change
(quasiquote fold) makes the rotation land where change happens — the same
rationale that put backend under the S110 lens mid-centrepiece. The assessment
should ALSO carry the frontend leg of the Principle-24 sweep (§4) and can
sanity-check the fold's contract claims (`lib.rs:48`, `frontend.md:127`) become
true. Dispatch timing: post-quasiquote-landing (ordering constraint 4).

### 8. `design/arch/` triage (Phase-2 duty)

`backend-keyed-consumer.md`: archive trigger substantively MET (S110 delivered
the bootstrap R-2 tail), but the physical move stays **PARKED one more sprint**
— S111 actively cites it (§9 pinned acceptance for the R2 negatives; FIXME 0621
cites §1.1.2). Execute the move at S111 close, updating the
`design/arch/CLAUDE.md` row and re-pointing the two citations in the same
commit. No other archive candidates: the working set is otherwise current;
`ownership-inference.md` stays live (it is the §3.7 authority this sprint
implements).

### Sign-off

Scope **APPROVED for Phase 3** with the adjustments above: (1) quasiquote wave
= frontend fold + int shield, one logical wave, shield ≤ fold; (2) 0621 rides
the schema-20 bump in the SAME change-set; (3) wave order per §1; (4) the §5
matrix axes are binding input to the `/design`(typecheck) + `/qa` Phase-3
plans; (5) 0553 deferred on the named trigger; (6) rotation confirmed frontend.
`/arch` Phase-3 actions carried forward: author the two pinned types diffs in
their implementing waves (MayAliasOf + schema-20 cascade; fallible
`allocate_got_slot` + exhaustion error), the quasiquote seam manifestation
(frontend rustdoc + BC §1/§6 sentences), and the `ResultMode` exhaustiveness
exception record.

**Next skills:** `/sprint` — Phase 3 dispatch: `/design` (typecheck — §5 axes 1–3
+ 0628), `/qa` (0623 matrix + P24 pattern battery + R2 rows + 0613 interaction
rows), `/testing` (0613 matrix), then the Phase-4 wave plan per §1 ordering.

## Skill plans (Phase 3)

_pending_

## Waves (Phase 4)

_pending_

## Dispatch log

_pending_

## Notes

- Baseline at S110 close: 4,590 passed / 7 known carries / 1 skipped. No source commits
  since close (git status: only cache + archive files) — baseline intact; verify at Phase-5 start.
- 4th-consecutive-audit backend items (build_isa, dispatch funnels, drop-glue, GOT) — **user ruled
  SHIP ALL** (2026-07-17); no 3rd deferral. GOT is the release-phase UB priority.

## Outcome (Phase 7)

_pending_
