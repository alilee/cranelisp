# Sprint 111: vec-assoc COW ownership root + backend audit-debt drain + quasiquote normative

Status: PHASE 4 COMPLETE — waves organized, both /arch rulings landed; ready for PHASE 5 (awaiting user go-ahead to launch implementation)
Audit: cranelisp-frontend (rotation — longest since assessment, s87; /sprint sets final target at Phase 4)

## Phase-1 decisions (user-approved 2026-07-17)

1. **Breadth: BROAD** — centrepiece + full backend audit drain + quasiquote + Principle-24 sweep + adjacent carries. Decomposed into waves.
2. **0613 quasiquote: ruled (A) LEGAL EVERYWHERE.** Quote/quasiquote desugar wherever an expression is legal. Typecheck/backend see no quasiquote (no new special form, no typing rule). **`/arch` Phase-2 correction:** NOT sole-frontend — `src/expander.rs::expand_scoped` (Pass-1 macro expansion) runs before `build_forms` and recurses into all sub-lists with zero quote handling, so a naive fold would let `(defn f [] '(m x))` (m a macro) silently corrupt the quoted literal. Fix = fold `expand_quasiquotes` into `build_form` (frontend) PLUS an int-side quote shield (hold `quote` verbatim; under `quasiquote` descend only into `unquote`/`unquote-splicing`). Two `/dev` surfaces (`cranelisp-frontend` + `src/`), one logical wave; `/testing` matrix gains quote × macro-expansion interaction rows. 0614 becomes a `/stdlib` no-op; 0615 rides.
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

## Skill plans (Phase 3) — 2026-07-17

Full detail lives in each skill's owned design docs; this is the coordination synthesis.

### /arch — cross-crate interface pins (design/arch/*, cranelisp-types rustdoc; NOT landed — coupled to implementing waves)
- **`ResultMode::MayAliasOf(usize)`** pinned as exact diff (`interfaces.md` §"Ownership-inference carriers" + `ownership.rs` rustdoc). Serde-visible → `CACHE_SCHEMA_VERSION` 19→20, **0621 rider inside the one bump window**. Consumer census: ONE compiler-forced exhaustive match (`transfer.rs:592–609`); exactly TWO grep escapes both safe-direction (`return_is_fresh_by_summary`, `is_abi_conservative`) — no third. `#[non_exhaustive]` deliberately absent (P18 exhaustiveness = the safety feature); exception recorded in `ownership.rs` rustdoc + types `CLAUDE.md`.
- **GOT R7** pinned schema-INDEPENDENT: `allocate_got_slot(&mut self) -> Result<usize, GotExhausted>` (no bump on failure). **Caller census corrected: 10 typecheck fallible sites** (Phase-2 table missed `program/register.rs:376`+`:948`) → ONE typecheck `CheckError` mapping helper (P7); 3 bootstrap `unreachable!`; int `redefine.rs:254` (existing S101 guard collapses onto the Result).
- **Carrier-completeness matrix** authored as binding `ownership-inference.md` §3.7.1 (4 axes). Reachability probes = **FIVE** (not "twins": `result_unique_of` `fixpoint.rs:413` included); `confinement.rs:162` is not a sixth (routes through site 2).
- Quasiquote BC currency: `bounded-contexts.md` §1 invariant 10 (fold) + §6 quote-shield sentence; `lib.rs:48` claim becomes TRUE.
- Filed **FIXME 0632** (P24 sweep battery inputs → /qa); /qa produced the register (0632 resolvable at its close).

### /spec — DONE (both FIXMEs user-ratified dispositions; no normative question opened)
- **0630 DELETED** — §5.1.2 multi-sig example fixed to concrete `(Vec Int)`/`(List Int)` (bare `:Vec` under-specifies; S109 assert-not-acquire) + explanatory paragraph tying to the section's own two rules.
- **0613** — new `spec/09-macros.md` §9.4.4 "Legal Wherever an Expression Is Legal" (reader sugar, desugars every form to `macros/Sexp*` ctor application yielding `Sexp`; no new special form/typing rule; unquote/unquote-splicing still §9.4.2-governed). Coverage band left to /qa.

### /design (typecheck) — schema-20 a1/a3 + 0621 + carries (design/typecheck/*)
- **a3 fix = ONE shared prelude-hop helper** on `TypeCheckEnv` delegating to `scope_resolve_in` (`checker.rs:1037`) — prelude fallback + import-chain + I-1 filter intrinsic to `ResolutionScope::resolve`, hand-rolls nothing. All 5 `fixpoint.rs` sites (`:77/:89/:393/:402/:413`) call it. **No sixth site** (confinement/transfer route transitively).
- **a1 producer arm** `origin_to_result_mode` (`transfer.rs:237`): BOTH `MayParam` arms → `MayAliasOf(i)` (`{projection:false}` at `:237` + `{projection:true}` at `:248`, was `ProjectionOf`). **/arch CONFIRMED** (2026-07-17) — completes §3.7's reservation clause; hard `AliasOf`/`ProjectionOf` reserved for unconditional claims only.
- a1 consumer transfer-join arm (`transfer.rs:591`): `join_origin(Fresh, arg_origins[k])` (0520 rule); only exhaustive `ResultMode` match in crate → variant axis closed by compiler. Increment-II (`uniqueness.rs`) unaffected.
- **0621 rider**: `checker.rs:1468` `resolved.fq` → `storage_fq()`, same change-set as schema bump.
- Carries: **0628** HKT-on-primitive — root cause is HKT-ness derived from method-body usage (bare con_var invisible); fix = derive from declaration + arity-independent non-type-constructor rejection. **0595** two P18 hardenings (not live-reachable). **0590** substantially LANDED already; R1/I2 residual is a `/dev` correctness item with a binding never-error-arm guard.

### /design (backend) — audit drain R4/R5/R6/R7 + COW currency (design/backend/audit-drain-s111.md NEW)
- **R5 splits byte-identical** (empty `CRANELISP_CODEGEN_DUMP` corpus diff is acceptance): `compile_resolved_call` ~325→~35 ln (3 moves incl. 2 P7 dedups); `compile_to_module_impl` ~395→~40 ln (5 phase helpers, lands AFTER R4 §1.4).
- **R4 one change-set**: delete dup `build_isa`; Wave-2b shim removal; **delete** `compile_defn` harness path (re-seam CLIF probe through production seam); drop `module_aliases` (`pub compile_to_module` sig moves).
- **R6** drop-glue: shared `emit_drop_glue_fn` envelope + 3 named naming fns (identity test calls them, not inline `format!`).
- **R7 census CORRECTION**: `extern_call.rs:151` is a **`#[cfg(test)]` fixture** — backend has **ZERO production `allocate_got_slot` sites**. **Open /arch decision: is `store_slot` a checked Result (backstop) or exhaustion refused at allocation seam only?** /design recommends allocation-seam-primary + cheap always-on `store_slot` backstop. **→ routed to /arch.**
- Item 5: `MayAliasOf` changes NO emitted instruction (COW machinery byte-stable — only flips which bodies keep already-emitted protect); belongs to centrepiece wave. `backend.md` truth pass done (retired-facade cites repointed, `FunctionArtifacts` overclaim corrected, keyed-consumer end-state added).
- **R8 archive moves NOT executed** (deliberate — prior curation kept some as cite-with-care); **/sprint to confirm disposition** + `git rm` FIXME 0096 (§9 marks DONE).

### /design (frontend) — quasiquote fold (design/frontend/quasiquote-fold.md NEW)
- Fold `expand_quasiquotes` into `build_forms`/`build_form` (first step, before `:Type` pairing). `build_expr` does NOT fold (internal recursion primitive, zero prod direct callers) — keeps backstop. Idempotent fixpoint → `macro_clause.rs:67` caller **retained harmless**. Zero public-API diff; `lib.rs:48` claim becomes TRUE.

### /design (int) — quote shield (design/int/quote-shield.md NEW)
- Two guard clauses at top of `expand_scoped` non-empty-list arm: Rule Q (`quote` verbatim, no descent); Rule QQ (`shield_qq` depth-tracked walker, expand only live unquote/unquote-splicing bodies). **~40–55 ln** (arch's ~15 was guard-core only). Recognizes quote family by SAME structural test as the fold (lockstep, never double-desugar). **Shield lands ≤ fold** (shield-only inert-safe; fold-without-shield opens corruption). One logical wave, two `/dev` surfaces.

### /qa — sprint-wide failing-test plan (tests/plan/PLAN.md §S111 + risks.md + s111-principle24-register.md) — EXIT GATE PASS
- **0623 + 0591 FIXMEs DELETED** into PLAN §A / §G.4. Every unit-tier deferral enumerates its cases; standing REDs named as wave acceptance.
- §A vec-COW: 4 committed REDs (CW-1..4) + 7 new cells + Fence-2 (copy-arm exactly-one-count) + Fence-3 (declared-fact reachability twin). §B carrier-completeness (15 reachability cells + whole-table `MayAliasOf`=={vec-set,vec-push} pin). §C quasiquote 3×3×2 + all 8 interaction cells + nesting depth + backstop. §D GOT boundary (1023/1024). §E R2 hard-miss negatives (must-author-FIRST). §F P24 battery (primitives/intrinsics/platform CLOSED grep-zero; 11 int sites pre-listed; `jit.rs:117` lean = structural tie-error). §G carries (0604 foreground repro; 0590 R1; 0595; 0591 ruled §2.3.8/§3.9 violations). §H R4/R5 byte-identity gates.
- **ESCALATION VALVE:** CW-F3a (explicit-import control) is a verification probe, authored FIRST — if RED at HEAD the declared-fact reachability gap is wider than §3.7 states; **/arch hears before the ownership wave lands.**

### Open items — RESOLVED for Phase 4
1. **/arch decisions — BOTH RULED (2026-07-17):**
   - `MayParam{projection:true}` collapse **CONFIRMED** — end-state producer table: BOTH `MayParam` arms → `MayAliasOf(idx)` (completes §3.7's reservation clause — the `projection:true→ProjectionOf` arm at `transfer.rs:248` was the same honesty defect one arm over); unconditional `Root→AliasOf` / `Projection→ProjectionOf` stay (flagship accessor precision untouched). Variant claim widened to "fresh OR reaches into param *i* (the param or a view rooted in it)"; both consumer reads verified indifferent to identity-vs-view at the May point (retain-side-only, zero soundness exposure).
   - `store_slot` shape **RULED**: `Result`-shaped `store_slot` **REJECTED**; instead `GotTable::store_slot`/`load_slot` (`got.rs:135/:146`) promote `debug_assert!`→**always-on `assert!`** (signatures unchanged) — an in-process OOB index is an invariant breach (compiler defect) → located hard-fail, not release UB, not a laundered `Result` (P18/P20/P6). The ONE genuine untrusted source — cache-deserialized `.meta.json` `got_slot` — gets the **diagnosed error at the cache-load trust boundary** (`got_slot < GOT_TABLE_SIZE`; violation ⇒ cache-stale → recompile). **Companion obligation routed /design(backend), same R7 track / same change-set.**
2. **/sprint dispositions:** R8 archive moves + `git rm` 0096 → confirmed, execute in CS-1; 0591 → rides CS-3 quasiquote wave; 0604 firing environment → provide to /testing at Stage 1.
3. **Census for Phase-4 waves:** R7 = 10 tc callers + **0 backend production** (`extern_call.rs:151` is `#[cfg(test)]`); reachability = 5 sites.
4. **Wave-org note (/arch):** R5 funnel-split should keep `lib.rs:994` stable, else the GOT-backstop change-set re-anchors that line reference.

## Waves (Phase 4) — 2026-07-17

**Structuring constraint:** worktree isolation is broken → **one source-touching agent at a time** (root CLAUDE.md §Testing). So Phase-5 "waves" are an ordered **serial pipeline of atomic change-sets**; only read-only work (the P24 sweep, /qa planning, /audit) parallelizes. Ordering also obeys /arch §1: R2 negatives → backend byte-identical → schema-20 ownership LAST (emission-affecting, scoped re-baseline as its final act); quasiquote shield ≤ fold; GOT schema-independent/early.

### Phase 5 Stage 1 — QA-first failing set (one /testing invocation, sprint-wide)
`/testing` authors the full RED set to `tests/plan/PLAN.md §S111`, in /qa's stated order: **CW-F3a FIRST** (the declared-fact-reachability verification probe — if RED at HEAD the gap is wider than §3.7 states, escalate to /arch BEFORE the ownership wave); **R2 hard-miss negatives must-author-first** for the backend track; then the remaining matrices (vec-COW CW-1..11 + fences, quasiquote QQ + 8 interaction cells, GOT GE-1..4, 0628/0590/0595 pins, 0604 foreground repro IR-1). Failing-not-ignored. `/sprint` provides the 0604 firing environment.

### Phase 5 Stage 2 — serial change-set pipeline (each: /dev → /review; iterate per crate)

- **CS-1 · Backend byte-identical drain** (R4 hygiene + R5 splits + R6 drop-glue). `/dev`(backend) → `/review`(backend). Acceptance = empty `CRANELISP_CODEGEN_DUMP` corpus diff (byte-identity), not just green suite. FIRST so it lands on a clean golden baseline before any emission change. (R8 archive moves + `git rm` FIXME 0096 ride here — /design(backend) deferred the physical move for /sprint confirmation; confirmed: execute in CS-1.)
- **CS-2 · GOT exhaustion (R7)** — schema-INDEPENDENT, early. `/arch` lands fallible `allocate_got_slot` + `GotExhausted` in `cranelisp-types`; `/dev`(typecheck) the 10 fallible callers via ONE `CheckError` mapping helper; `/dev`(backend) promotes `store_slot`/`load_slot` `debug_assert!`→**always-on `assert!`** (signatures unchanged) PLUS the **cache-load-seam `got_slot < GOT_TABLE_SIZE` validation** (violation ⇒ cache-stale/recompile — the diagnosed error at the one untrusted boundary; same change-set). Boundary test GE-1 (1023/1024). Keep `lib.rs:994` line-stable across the R5 split or re-anchor. → `/review`.
- **CS-3 · Quasiquote** (one logical wave, two surfaces, **shield ≤ fold**): `/dev`(int) quote shield in `expand_scoped` FIRST-or-same-change-set, then `/dev`(frontend) fold into `build_forms`/`build_form`. **0591 rides** (same /dev-frontend surface — /qa ruled it §2.3.8/§3.9 violations). → `/review`(frontend) covering both legs + the 8 interaction cells (QQ-I1..I4 the corruption/over-shield guards).
- **CS-4 · Typecheck adjacent carries** — 0590 R1/I2 (safe-direction wrong-reject, against the recorded guard), 0595 (two P18 hardenings), 0628 (HKT-on-primitive: HKT-ness from declaration + arity-independent rejection). `/dev`(typecheck) → `/review`. Kept before the centrepiece so typecheck changes stay incremental and the big re-baseline is isolated.
- **CS-5 · Schema-20 COW centrepiece (LAST — emission-affecting)** — ONE coordinated change-set: `/arch` lands `ResultMode::MayAliasOf(usize)` + `CACHE_SCHEMA_VERSION` 19→20; `/dev`(primitives) truthful `ownership_facts.rs` (whole-table sweep, not 2-row patch) + CLAUDE.md declared-facts contract; `/dev`(typecheck) the ONE shared prelude-hop helper + a1 producer/consumer arms + **0621 rider inside this bump window** (+ /arch's projection-collapse ruling, open item 1); `/dev`(backend) rustdoc currency (no instruction change). → `/review`. **Scoped + attributed golden re-baseline is the wave's LAST act** (S102 §6.2) — invalidates caches wholesale; drift beyond the COW class is expected (a3 activates inert increment-I precision). Flips the 4 RED carries + 0623 matrix green.
- **CS-6 · 0604 index-race fix** — after IR-1 repro lands; foreground-attributed (not the index feed). Owner set at repro (likely `/dev` int or typecheck per attribution).

### Read-only lane (parallel, no ordering constraint) — Phase 6 timing for the frontend leg
- **Principle-24 sweep**: `/qa` owns the compiler-wide register (`tests/plan/s111-principle24-register.md`); typecheck → int legs classified as their change-sets settle; **`/audit` frontend rotation carries the frontend leg in depth AFTER the quasiquote fold lands** (end-state lens, S110 post-W3 precedent). Backend already classified (s110 audit §2.1 — cite).

## Dispatch log

All via agent-type shims (model/effort pinned per artefacts.md §II.3); all default-tier unless noted.
- **P2**: arch × scope review — default (fable/xhigh). Committed `5b57f4ed`.
- **P3** (parallel, read-only design surfaces, no-commit → /sprint batch commit): arch × interface pins; spec × 0630+0613; design × typecheck; design × backend; design × frontend; design × int; qa × sprint-plan — all defaults.
- **P3 follow-up**: SendMessage → arch (resume) for 2 rulings (projection-collapse; store_slot shape) — default.
- No model-tier escalations. No named fallbacks.

## Notes

- Baseline at S110 close: 4,590 passed / 7 known carries / 1 skipped. No source commits
  since close (git status: only cache + archive files) — baseline intact; verify at Phase-5 start.
- 4th-consecutive-audit backend items (build_isa, dispatch funnels, drop-glue, GOT) — **user ruled
  SHIP ALL** (2026-07-17); no 3rd deferral. GOT is the release-phase UB priority.

## Outcome (Phase 7)

_pending_
