# Sprint 111: vec-assoc COW ownership root + backend audit-debt drain + quasiquote normative

Status: PHASE 5 CONCLUDED (2026-07-17) — awaiting /sprint+user ship judgment + 3 decisions (0641 scope, 0628, I-C), then Phase 6. Declared scope DELIVERED; all 16 REDs attributed to open defects w/ owner+trigger, zero genuine regressions.

## Phase-5 conclusion — /qa attribution close (`e8737c94`, PLAN §I.4)
- **CS-6 (0604): CARRIES — seam NOT locatable** (~320 cumulative no-fires all regimes; only S109-era /sprint env ever fired; MODULE_TRACE recipe inoperable — foreground install path uninstrumented). Static narrowing done (poison = public `bit-and` head in prelude's LIVE table at super-import install; no enumerable writer produces it → hides in concurrency plumbing or already removed by S110/S111). **Follow-up first step (bundled into carry): observability — a MODULE_TRACE emit / `debug_assert!` at live-table insertion enforcing "prelude gains no entry outside its exports post-compile"** so the next firing names the seam. IR-1 stays the env-bound guard.
- **R2 → 4th ATTRIBUTION (final): entry-`main` IO-box teardown leak** — NOT drop-glue/§3.7/vec-element-drop. `(defn main [] (let [s "hi"] (Pure 9)))` → 2 alloc/1 free (leaked = the IO-result alloc; ownership-independent; non-main fns balanced). Deterministic 2-line repro. Owner /dev(backend main-epilogue / int IO-trampoline result-dec). **CARRY** (deterministic repro guards it; /testing owes re-annotate `class=rc-miscount locus=entry-main-IO-teardown` + repro swap) — this-sprint-fixable if user directs, else follow-up.
- **0641 split confirmed:** B-1/I-1 = /dev(typecheck) inference half; **B-2/I-2 = /dev(backend) vec-set-RESULT consume seam** (toggle-off yields WRONG VALUES 55-for-99 / 190-for-9 — ownership-independent, the increment MUST pair a backend fix; typecheck provenance alone can't flip these 4).
- **0638:** distinct macro-clause-invocation corruption (int `expander.rs` invoke core + `marshal.rs`); symptom-polymorphic (double-free→"match failed"→SIGSEGV); /testing owes the narrow repro. Carry.
- **I-3 renamed-import: PRE-EXISTING SINCE SPRINT 9** — §8.3.5 never implemented (no parser arm, no `ImportNames::Renamed`); carrier reshape → /arch → own increment. Carry.
- **RED-integrity CLEAN:** 16 REDs all trace to an open defect w/ owner+trigger; suite 4674 pass / 16 fail / 1 skip; stdlib gate GREEN. Zero genuine regressions.
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
- **P5-S1**: testing × sprint-wide failing set — default (opus[1m]/high). Committed `ce0124b2`.

## P5 progress

**CS-1 backend drain LANDED (`522c66e5`) — /review dispatched.** Byte-identity EMPTY DIFF (23-frame corpus, re-verified per sub-wave); KC-N1..N6 all GREEN on write (seam hard-fails as designed — no gap); suite unchanged (4602 pass / 32 fail = 25+7 / 1 skip; no backend-codegen RED). R4/R5/R6 + R8 (no-op, docs already archived). Flags → dispositions:
- **F1 `store_slot` moved `lib.rs:994`→`1104`** (R5 phase split, line-stability infeasible) → **CS-2 GOT backstop re-anchors the `assert!` promotion at `:1104`** (noted in CS-2).
- **F2 CacheMetadata envelope collapse DEFERRED** (R4 §1.2 remainder — cross-surface backend+int, ~7 cache read sites, own public-api regen, ZERO emission impact) → **/sprint disposition: fold into CS-2 backend leg** (same /dev-backend surface, adjacent cache cleanup) OR its own micro-CS; decide at CS-2 dispatch.
- **F3 `audit-drain-s111.md §1.2 exe.rs premise factually wrong** (`generate_startup_object` is DEAD in backend — relocated to int at S76 §4.4; only `exe/tests.rs` reaches it) — /dev filed FIXME → /design(backend); disposition (delete orphan vs keep as test-ref) is a /design call, **not blocking**; kept honest `#[allow(dead_code)]`.
- **F4** backend-keyed-consumer.md must NOT move (KC-N tests cite §9) — already parked to /arch Phase-7.

**CS-1 /review CLEAN (`aa0b743`, no Blockers).** Byte-identity INDEPENDENTLY re-verified 18/18 programs (HEAD~1 vs HEAD); mirrors genuinely collapsed (build_isa single-source, R5 P7 dedups real, R6 envelope unifies closure+curry); `compile_defn` re-seam lost no coverage. Five Importants disposed → FIXMEs filed:
- **I1 → FIXME 0633 (/qa):** ADT drop-glue name keys on bare `fqtn.name` (drops module + concrete-args) — latent 0350/ledger-25 silent-mis-drop class on name×instantiation + name×module axes; **CS-1 canonized it as correct in new rustdoc + a test (a FALSE guard masking a real defect).** /qa assess reachability + repro → /dev correct the false assertion (now) + re-key if reachable; /design fix the claim. Fix-vs-carry = /sprint call post-repro.
- **I2 → FIXME 0634 (/dev):** CacheMetadata envelope collapse — **belongs in CS-5's schema 19→20 bump** (persisted-serde, NOT byte-identical CS-2 as first planned; /review corrected). Added to CS-5 scope.
- **I3+I4 → FIXME 0635 (/design):** `audit-drain-s111.md §1.2` exe.rs premise factually wrong (backend `generate_startup_object` DEAD, relocated to int S76 §4.4); + `implementation-slice-s66.md` archive move (the CS-1 R8 rider that didn't run; 0096 ref stale). Non-blocking.
- **I5 → FIXME 0636 (/qa):** L-B1 golden lane 10/13 STALE (pre-CS-1 drift, S103 baseline) → **CS-0.5 lane re-baseline (attributed) BEFORE CS-5** — else CS-5's attributed re-baseline is unreadable. Inserted in pipeline.
- Suggestions S1 (identity test wants a Module-level FuncId drive, not name-equality) / S2 (probe-vs-production `func_ids` seed divergence) / S3 (record the 18-program evidence) / S4 (pub(crate)→pub(super)) — noted, low-priority, roll to CS close or carry.

### Pipeline update (2026-07-17)
- **CS-0.5 · L-B1 golden lane currency** (NEW, gates CS-5): /qa verifies the 10 drifted frames are benign already-landed churn → /testing re-baselines to HEAD. FIXME 0636.
- **CS-5** now also carries the CacheMetadata envelope collapse (FIXME 0634) on the schema-20 bump.
- 0633 corrective (false-assertion fix + possible re-key) slots per /qa repro outcome.

### 0633 verdict: REACHABLE → CS-1.1 pulled into scope (2026-07-17)
`/qa` read-only assessment (`be22ecb9`, plan `tests/plan/s111-0633-adt-drop-glue-underkey.md`): **REACHABLE, both axes, all 3 modes.** TWO under-keyed layers (not one): `adt_drop_glue_name` (`resolution.rs:114`) AND `build_elem_dec_fn` (`vec_codegen.rs:734-738`), both bare-`fqtn.name`-keyed with first-build-wins `get_name` skips. Body is per-INSTANTIATION (concrete_args substituted before per-field heap classify), so the key under-determines. Collision scope = one `compile_to_module` batch; a SINGLE defn body suffices: `(Vec (Pair Int Str))` + `(Vec (Pair Str Int))` dropped in one `let` → `atomic_rmw Sub` on raw Int (SIGSEGV/corruption) + Str leak; order-dependent (fails P24 acid test). Latent REPL-vs-`.o` divergence (batch cardinality). Nothing upstream disambiguates; typecheck NOT implicated. Non-vec ADT path (inline glue) does NOT collide.
- **Decision (/sprint): FIX this sprint** — reachable memory-safety defect in the R6 drop-glue area this sprint hardens; evidence-gated (repro shape known); single-crate backend. NOT a scope pivot — it's the honest completion of R6.
- **CS-1.1** (NEW, EMISSION-AFFECTING — re-keying changes emitted `Linkage::Local` glue symbol names → golden drift; sequence AFTER CS-0.5 lane currency, attributed re-baseline): /testing commits failing REDs FIRST (0633-R1 concrete-args single-defn PRIORITY, 0633-R2 module axis, 0633-R3 corrected identity battery) → /dev(backend) re-keys BOTH layers on a mangle of full `Type::ADT(fqtn,args)` (module+name+concrete-args) + corrects the false rustdoc/test assertion → /review → /design(backend) corrects `audit-drain-s111.md §4` canonized claim (FIXME 0633 body). The false-assertion correction is MANDATORY regardless of fix timing (a false guard masking a SIGSEGV is itself a defect).

**CS-2 GOT exhaustion LANDED (`ef62f10e`) — /review dispatched.** Atomic 31-file cross-crate; workspace compiles at commit (atomicity gate held); `CACHE_SCHEMA_VERSION` stays 19 (confirmed not serde). GE-1..3 GREEN; suite 4606 pass / 32 fail (unchanged 25+7) / 1 skip = +4 (the GE tests), no regression. Per crate: types (fallible `allocate_got_slot` + `GotExhausted` + `assert!` promotion, per pinned diff verbatim); typecheck (10 callers via ONE helper `result::got_exhausted_error`, 3 bootstrap `unreachable!`); backend (cache-load `CacheStale::GotSlotOutOfRange` validation); int (`redefine.rs` guard collapsed onto Result). Flags → /review:
- **G-F1 (deviation from pin):** helper returns `CranelispError::CodegenError` NOT `CheckError` (no `From<CheckError>`; chains thread `CranelispError`; lifted at `check_forms` boundary). /review gates soundness; round-trip to /arch only if it judges it a design deviation not sound-plumbing.
- **G-F3 `clippy::result_large_err`**: 8 new, left un-annotated (consistent w/ ~400 un-annotated typecheck siblings; rustc gate clean). Note-only.
- **G-F5 /arch-owned lockstep NOT swept:** `sequences/exec-flow-redefine.mmd:31` + `interfaces.md:1259` SymbolTable impl-sketch still show the infallible signature (pinned diff below is authoritative). → **/arch follow-up** (regen at CS-5 types-landing or Phase-7; low-pri, pinned diff governs).

**CS-3 quasiquote LANDED (`9a9fb8c4`) — /review dispatched.** Atomic (int shield + frontend fold + 0591), byte-stable (goldens incl. `golden_clif_w0b_macro_clause` pass — new compiles, no drift), defmacro control stays GREEN. **15 REDs flipped (32→17):** QQ-1..4 desugar (7), QQ-I1/I2/I5/I6 corruption/over-shield guards (5), AP-2/3/4 (3). 4 expected flips did NOT happen — each external to CS-3 correctness, routed:
- **SG-1 did NOT flip — 0614 is a REAL /stdlib fix, not the no-op /arch predicted.** After the fold `derive.cl` compiles past the parse error but hits a SECOND latent §9.3.4 violation: `derive-Eq/Ord/Display` reference `build-impl-target` (same-module `defn-`) in a live unquote ("macro expansion may not reference same-module non-macro definitions"). → **/stdlib: move `build-impl-target` + expansion-time siblings to a dependency module** (a Phase-5 defect fix; flips SG-1). Correct the P5-progress "0614 no-op" expectation.
- **QQ-I3/I4 = broken /testing FIXTURES, not a shield bug** (pending /review independent confirm): fixture macro bodies return the Sexp *value* (`(SexpInt 999)` → expands to bare `Int`), so `~` correctly type-errors per §9.4.2 (unquote result must BE `Sexp`); /dev proved a well-typed twin (`(quote (macros/SexpInt 999))`) expands correctly + unit `quasiquote_live_unquote_expands_macro` GREEN. → **/qa+/testing: fixture bodies must produce the constructor CALL sexp, not the raw value** (after /review confirms shield semantics).
- **AP-1 = frontend leg DONE, typecheck defect remains** — multi-arity per-clause independent check rejects a free-var (`:a`) param single-arity `defn` accepts (FV-6 GREEN); SIBLING of 0590 R1/OA-1 ("not pinned" in `finalize.rs`). → **fold into CS-4** (typecheck).

**CS-3 /review CLEAN (`a2680213`, no Blockers).** Load-bearing verdict INDEPENDENTLY verified by execution: **QQ-I3/I4 are FIXTURE bugs, NOT a shield defect** (the `Int`-vs-`Sexp` error proves the shield descended + expanded; an over-shield would throw unresolved-symbol). Fold idempotence sound (no un-desugared path to `build_form_inner`; `macro_clause.rs:67` now a no-op leg); byte-stability confirmed; shield coverage structurally complete; 0591 parse fix no mis-parse. Duplication verdict: `shield_qq`↔frontend depth math is a JUSTIFIED mirror (2 sites, cross-boundary, byte-identically pinned). Findings → **/testing fixture batch** (below):
- **I-1 (/testing):** QQ-I3 body → `(quote (macros/SexpInt 999))`, QQ-I4 → quoted `SCons` call (twins verified GREEN). Flips the 2 REDs.
- **I-2 (/testing):** QQ-I1/I1b/I2/I5 use `(defmacro m [x] 999)` — ill-typed per §9.5 (guards not vacuous but fail in the wrong mode + carry an unrelated type error). Use a well-typed macro.
- **S-5 (/qa+/testing):** add ONE nested-depth agreement row with a registered well-formed macro (closes the shield↔frontend silent-divergence residual; the intended QQ-I5 pin was weakened by I-2).
- **S-3 (/dev frontend, low-pri):** idempotence test uses `format_flat` — assert span-inclusive. **S-4 (/dev int, low-pri):** `shield_qq` `Option<bool>` magic bool → extend `QuoteHead` enum. Both roll to CS-3-follow or close.

**/testing fixture+repro batch LANDED (`9371f9f2`, test-only, no re-review needed — applies /review-verified fixes + new RED guards).** QQ-I3/I4 GREEN (52/52 spec_09); QQ guards well-typed (fail only on shield regression now); S-5 depth-agreement cell GREEN. **0633 R1 DETERMINISTIC** (SIGBUS 6/6 all faces once vecs are live — asserts clean observable value/exit, NOT signal; **3 guards REPL/`--run`/`--link` — collision scope differs per path, so CS-1.1 must cover all three** incl. the REPL-vs-`.o` divergence) + R2 leak face (alloc/free imbalance). **Baseline 17→19** (−2 QQ green, +4 0633). /qa bookkeeping flags: ratify `// defect:` class `drop-glue-underkey` (or map to `uaf`/`rc-miscount`); update plan rows 0633-R1/R2 status. → batch into a later /qa touch (CS-0.5).

**0614 RESOLVED (`539fdd4d`, /stdlib) — SG-1 GREEN, baseline 19→18.** 41 derive helpers → new `derive.helpers` dep module (7 public entry points, 34 private); §9.3.4 chain fully cured; qualified `sconcat`→`macros/sconcat` (2nd latent bug); FIXME 0614 deleted. **NEW DEFECT surfaced → FIXME 0638 (/qa):** derive macros COMPILE but **double-free/SIGSEGV at INVOCATION** — the macro-clause JIT path + a helper returning a deep interior alias (`dt-body` returns `rest`). Reachable memory-safety; plausibly a sibling of the §3.7 COW-UAF / 0633 interior-alias family. Minimal deterministic non-stdlib repro PRESERVED verbatim in FIXME 0638 (scratchpad was ephemeral). Plan: /qa attribution → /testing narrow repro → **RE-CHECK after CS-5** (if §3.7 ownership fix cures it, attribute + regression-row; else distinct → /dev backend/intrinsics, fix-vs-carry /sprint call). This is the "0605 tier-2 follow-on" 0614 deferred — now LIVE, not just missing coverage.

**CS-4 typecheck LANDED (`3b151a05`) — /review dispatched.** Four items GREEN: I-1 (CS-2 diagnosed-error rendering — explicit `CodegenError` arm + boundary-surface pins closing the GE-3 miss), OA-1 (0590 R1 resolved-overload benign exemption), AP-1 (multi-arity clause-result written-var polymorphism — the `∩ result-type free vars` discriminator), 0595 (P18 rigid-unify + `infer_lambda` teardown). Byte-stable, typecheck-internal. **Baseline 18→15** (OA-1a/b + AP-1). **Item 5 (0628) REVERTED + ESCALATED → FIXME 0639** — /dev correctly refused to ship a red release gate.
- **0628 is a NORMATIVE QUESTION for /spec + USER (retarget 0639).** /sprint spec analysis (spec/07-traits.md): §7.1 grammar line 12 — the **parenthesized head `(deftrait (X a) …)` is UNAMBIGUOUSLY HKT syntax** ("higher-kinded trait, see 7.2"); §7.2.4 line 196 — "**Primitive types MUST be rejected as HKT impl targets**"; §7.1.1 line 67 — each method MUST have ≥1 param of the implementing type. So the 0628 gate is **spec-FAITHFUL**, and the ~7 green e2e tests using `(deftrait (Sizeable a) (size [a] Int)) (impl Sizeable Int)` are **spec-VIOLATING** (HKT syntax used as a kind-* parametric trait; the 0628 `Zeroable` `(zed [] :a)` ALSO violates §7.1.1's ≥1-implementing-param rule — empty params). But they've been green → de-facto accepted. The example is ILL-FORMED per the current spec (verify-example-before-fork lesson) — so the fork is NOT symmetric:
  - **(A) spec-faithful:** land the gate; migrate the ~7 e2e tests + ~24 unit fixtures to the bare-head `self`-form (`(deftrait Sizeable (size [self] Int))`); reject `(deftrait (X a))`-on-primitive. A coordinated /testing + /dev(typecheck) wave.
  - **(B) extend the spec:** a never-applied con_var in `(deftrait (X a))` means a kind-* parametric trait (valid on concretes incl. primitives). Requires a §7.1.1/§7.2 amendment + an "is con_var ever applied?" discriminator; then 0628's leak becomes a codegen defect to FIX (not reject), and the tests are valid.
  - **/sprint recommendation: (A)** — spec-faithful, no invented semantics; the tests encode a spec violation that grew green. Pending USER ruling (routed, non-blocking — 0628 is off the critical path).

**CS-4 /review — BLOCKER B-1 (memory-safety) + normative I-C.** I-1/OA-1/0595 verdicts CLEAN (I-1 correct+complete; OA-1 read-only safe-direction; 0595 byte-identical). **B-1 (BLOCKER):** the AP-1 discriminator (`finalize.rs:518-570`, `written-vars ∩ result-free-vars`) tests quantifiability NOT independence — a written var can reach the result AND be pinned by a delegating self-call; the drain then silently acquires the sibling's concrete types (spec §5.1.2 forbids this back-flow) + the published scheme claims genericity over an Int-specialized body. **Proven memory-unsafe** by execution: `(defn rp4 ([:a p :a rot] (let [q (rp4 p rot 0)] p)) ([:Int …])) (rp4 "x" "y")` → String heap ptr returned as Int (`202781896831488`); sibling `(add-i64 p idx)` → ptr arithmetic on a String. All rejected pre-CS-4 → wrong-accept OPENED by CS-4.
- **Disposition (/sprint): CS-4.1 REVERTS the AP-1 term** (restore multi-arity clause params to non-polymorphic — spec §5.1.2-faithful; OA-1 `benign_overload_vars` STAYS, only the `∪(written∩result-free)` term reverts). Eliminates B-1; AP-1 → RED (normative-pending). Chosen over /review's surgical veto because AP-1's acceptance is UNRULED semantics (contradicts §5.1.2) — default to the written spec until the USER rules I-C; re-land with the sibling-forcing veto IF the user rules "allow".
- **I-C → /spec + USER (2nd normative Q, coupled w/ 0628):** is multi-arity clause param polymorphism legal? §5.1.2 says NO (categorical); AP-1/FV-6 §3.9 symmetry argues YES (single-arity `(defn f [:a x] …)` accepts `:a` polymorphic — the asymmetry /review flagged). The discriminator's semantics were decided by MECHANISM not RULING. Surfaced to user; non-blocking.
- **I-A → CS-4.1 (/dev):** OA-1/AP-1 landed with ZERO finalize-seam unit tests (METHOD §2.2 violation — the exact gap that let B-1 slip). Add OA-1 seam units + /testing owes the B-1 neg matrix ({ascribed-result, returned-param} × non-Int call × 3 modes).
- **I-B → CS-4.1 (/dev):** P7 mirror — `collect_pending_overload_result_vars` hand-copies the drain's selection predicate; extract shared `select_unique_overload_variant` (3rd "resolved-dispatch benign vars" family member — per-variant-codepath growth).
- **I-D → /design (after I-C rules):** the discriminator has no design-intent record. **S-1 → CS-4.1:** `git rm` 0595 FIXME (resolved). **S-2 → CS-4.1:** fix `lift_error` comment over-claim.

**CS-4.1 LANDED (`9fdf3610`) — /review dispatched (adversarial B-1 hunt).** B-1 first vector reverted; `/dev` found + closed a SECOND independent vector (`/review` had cleared OA-1 as safe — it wasn't): rp2's `:a` body-ascription unifies the self-call return var with a PARAM var, so `collect_pending_overload_result_vars` returned the param and `benign_overload_vars` exempted it → same memory-unsafe accept. Structural close: subtract each clause's own param-type free vars from the benign set (param vars only, never result vars — keeps OA-1b's fresh `r` exempt). **Deviation flagged; /review must sign off + hunt a THIRD vector.** rp2/rp4 now REJECT cleanly; OA-1a/b GREEN; AP-1 RED (I-C-pending); I-A seam units (pos+neg) GREEN; I-B P7 `select_unique_overload_variant` extracted (drain+collector share); S-1/S-2 done. Baseline 15→16 (AP-1). Byte-stable, no schema.

**CS-4.1 /review — B-1 first two vectors CLOSED + param-subtraction SIGNED OFF; but found BLOCKER B-2 (THIRD vector, LATENT/pre-existing).** Adversarial hunt (10-probe table): rp2/rp4 confirmed reject; param-subtraction sound both directions (no over/under-subtract, OA-1a/b green, P9/P10 confirm no false-reject); P7 extract behavior-identical; I-A units genuine BUT would not have caught vector 2 (allowed-vars-composition seam) — the coverage-by-variants miss again.
- **B-2 (3rd vector, ROOT CAUSE):** `find_ambiguous_value_position` verdicts only CHILD positions (`for_each_child_expr`), so a LEAF-body clause (`([:a p :a rot] p)` bare Var, or a literal body) escapes the §5.1.2 param-pinned check ENTIRELY. `(defn rp15 ([:a p :a rot] p) ([:Int … ] (rp15 p rot))) (rp15 "x" "y")` → **String heap ptr read as `:primitives/Int`** (rev: Int read as String). §5.1.2 requires rejection. LATENT (independent of `allowed_vars`; predates CS-4). REPL-cross-batch-only for the unsafe READ (`--run` single-batch rejects via shared subst — itself a REPL/`--run` divergence); the bare leaf-body defn accepts in ALL modes. `refresh_multi_sig_variant_ret_types` (register.rs:236) refreshes RET only not params → persisted `(a,a)` params match any later-batch args.
- **ROOT-CAUSE FIX (the class-closing consolidation):** verdict the clause's PARAM TYPES directly — any residual free var post-subst → §5.1.2 error — subsumes rp4/rp2/rp15/leaf/unused in ONE structural check (P18/P20), replacing the body-position proxy + the allowed_vars/param-subtraction machinery. **Its predicate = the I-C ruling** (reject-if-any-free-var [spec-faithful] vs the sibling-forcing-veto-if-allowed).
- **DISPOSITION (/sprint): commit the repro matrix NOW (mandatory — protects CS-4.1 + records B-2); CARRY the structural fix (CS-4.2)** evidence-gated: pre-existing/latent + guarded-by-repro + coupled to the pending I-C ruling + the centrepiece (CS-5) has waited behind 6 carries. **I-C ELEVATED — it now governs a memory-safety class fix, not just AP-1 acceptance.**

### Emission-affecting ordering (refined)
Byte-stable change-sets first (CS-2 GOT, CS-3 quasiquote-enables-new-not-drift, CS-4 carries) → **CS-0.5 lane currency** → then the two EMISSION-AFFECTING change-sets each with its own scoped+attributed re-baseline: **CS-1.1** (drop-glue re-key) then **CS-5** (schema-20 ownership, last) → CS-6.

**Multi-arity §5.1.2 repro matrix COMMITTED (`03b8bf30`, /testing).** New `tests/multi_arity_clause_param_51_2.rs` (6 tests): rp4/rp2 GREEN rejection guards (protect CS-4.1 B-1 fix — no prior guard existed); lf1/lf2/rp15/rp19 RED B-2 wrong-accept guards (deterministic: DEFN-accept marker all-mode + rp19's stable `<invalid:1>` Int-as-String read; rp15's heap-ptr read narrated not asserted per no-flaky rule). Baseline **16→20** (+4 B-2). /qa bookkeeping (non-blocking, batch to a /qa touch): ratify `// defect:` class `wrong-accept` in `tests/CLAUDE.md` table; add PLAN.md rows for the 6 tests.

**CS-0.5 COMPLETE (`6122dbcf`, /testing).** L-B1 lane re-baselined to certified-sound HEAD (10 frames, −1191 golden lines, determinism self-test 13/13); **nextest gate `tests/clif_golden_lane.rs::clif_golden_lane_no_drift` landed** (shells the same `clif_golden.sh diff`, no 3rd extraction mirror; RED on any future drift = S102 §6.2 mechanically enforced). Vocab committed. Baseline 20 RED unchanged, +1 GREEN gate. **This is the attributed known-good baseline CS-1.1/CS-5 re-baseline as a clean delta FROM.**

**CS-1.1 drop-glue re-key LANDED (`34c223b4`) — /review dispatched.** Both layers (`adt_drop_glue_name` + `build_elem_dec_fn`) re-keyed on `adt_instantiation_mangle` (full `Type::ADT(fqtn,args)` via canonical `render_type` + the existing `inner_fn_discriminator_for` sanitize — NOT a new mangle; pub(crate), public-api byte-identical). **0633-R1 SIGBUS GONE** (exit 135→2, all 3 modes); 0633-R3 unit battery GREEN (distinct-args/distinct-module/distinct-nested⇒distinct, same⇒stable). NO re-baseline needed (drop-glue/elem-dec are inline aux fns, never captured as golden frames — byte-identical CLIF; lane gate GREEN). RC-balanced. **Baseline 20→17** (R1×3 green). False CS-1 assertion corrected. S-1 done (CLAUDE.md heading).
- **0633-R2 MIS-ATTRIBUTED (→ /qa re-attribute / /testing re-annotate):** /dev proved R2 does NOT reproduce the 0633 collision (fires single-module/single-ADT/single-vec, no collision possible) — it's the DEF-3/§3.7 temporary-heap-element consuming-convention leak → **flips at CS-5, not 0633**. Re-label R2's `// defect:` to §3.7/CS-5. The genuine module-axis collision IS pinned by the 0633-R3 unit cell.
- **S-3 deferred (public-API):** `read_cached_metadata` (`serialize.rs:389`) is on `public-api.txt:234` w/ tests — retiring needs public-api regen + /design canonical-surface update; orthogonal to the memory-safety re-key → /sprint slot later w/ /design.
- **/design(backend) flag:** `audit-drain-s111.md §4` keying discipline still says fqtn-keyed — correct to full-instantiation mangle (the /design half of 0633).

**CS-1.1 /review — BLOCKER B-1 (mangle NOT injective) → FIXME 0640 → CS-1.2 corrective.** Everything else CLEAN: both layers key identically CONFIRMED; NO third under-keyed layer (S-1: `poll_state_drop_glue` is a 4th glue name outside the naming home but correctly disc+span-keyed — low-pri); R2 re-attribution SUPPORTED (§3.7 temp-consume, flips at CS-5); byte-identity 13/13 lane green.
- **B-1/0640 (reachable SIGBUS against the FIXED compiler):** the sanitize (non-`[A-Za-z0-9_]`→`_`) is NOT injective — `-`/`?`/`!`/`.`/`/`/space all →`_`, and `_`→`_`. So `(deftype A-B …)` + `(deftype A_B …)` (hyphenated names are IDIOMATIC) mangle to ONE symbol → collision → SIGBUS (executed repro, `nm`-witnessed one glue serving both). The "same sanitize as `inner_fn_discriminator_for`" argument fails: mono consumers are ADDITIONALLY span+disc-keyed (span breaks sanitize ties); `adt_instantiation_mangle` is a pure content key with no disambiguator. The 0633-R3 battery uses only alphanumeric names → blind to the class.
- **CS-1.2 (/dev backend, fix now — same memory-safety class, hyphenated names common):** make the mangle INJECTIVE (prefix-free escaping — reserve `_` as escape, `_`→`__`, distinct escape per special char; OR content-hash suffix over the unsanitized render). Failing-first tests over the FULL reader-legal special-char set + module-axis (`a.b/T` vs `a-b/T`) — unit battery + e2e in `tests/adt_drop_glue_underkey.rs`. + S-2: `debug_assert!` concreteness at the mangle (a non-concrete `Type::ADT` would embed session-dependent `t{id}`). Delete FIXME 0640 on fix. Emission-affecting but not golden-captured (no re-baseline).

**CS-1.2 injective-mangle fix LANDED (`484be294`) — drop-glue class CLOSED.** Prefix-free escaping (`escape_symbol`: `_`→`__`, unique marker per special char, `_u{codepoint}` catch-all — injective by construction w/ a total decoder + round-trip-decode witness test). `A-B`/`A_B` SIGBUS GONE (exit 2 all modes; colliding pair == non-colliding control). Injectivity battery + 0640 e2e (name+module axis, 3 modes) GREEN. S-2 `debug_assert!(ty.is_concrete())` added. Lane byte-identical, RC == control, FIXME 0640 deleted. Baseline 17 unchanged (0633+0640 fully closed). **Accepted on by-construction injectivity proof (decoder witness) — no separate review cycle (the round-trip test IS the injectivity verification).**

### ★ CS-5 CENTREPIECE LANDED (`e99535e4`, 2026-07-17) — /review (adversarial) dispatched
The sprint's LEAD delivered. Atomic 4-crate, workspace compiles at commit. `ResultMode::MayAliasOf(usize)` + schema 19→20 + 0634 CacheMetadata collapse + primitives truthful COW facts (whole-table sweep = exactly vec-set/vec-push) + typecheck 1-helper/5-sites (no 6th) + both `MayParam`→`MayAliasOf` + consumer join (0520) + 0621 rider (storage_fq). Backend rustdoc-only (byte-stable). **§3.7 family flipped: `vec_assoc_param_mutate_return_uaf` 17/17 GREEN** (COW repro runs correctly, no corruption), + vec_cow_value_use_leak, ownership_fences (CW-F3b), ownership_reuse. **Baseline 17→8.** Carrier-completeness: 5 sites/1 helper/no-6th ✓, 1 exhaustive match + 2 safe `==Fresh` escapes/no-3rd ✓, producer whole-table sweep ✓. **Emission cert: NO golden frame drifted** (COW machinery byte-stable; lane GREEN, no re-baseline); differential all-Owned oracle behaviorally equivalent (toggle-off delta = expected conservative leak-tolerance, sound direction); RC vec_assoc 13/13 clean (DEC_CHECK). Unit tests all 4 crates (163/163 ownership); 7 pre-existing may-path tests updated for the producer-semantics change. 0634 actioned+reaped.
- **R2 THIRD re-attribution (→ /qa):** `adt_vec_drop_glue_module_axis_leak_r2` did NOT flip — byte-identical 5/4 before AND after CS-5, so NOT §3.7 either. It's a **vec-element drop-glue / consuming-convention leak** (heap-ADT element of a vec literal not dec'd at scope-exit). RED at clean HEAD (not a regression). /qa re-triage → likely /dev(backend) vec-element-drop.

### Baseline 8 RED (post-CS-5)
4× `multi_arity_clause_param_51_2` (B-2 → CS-4.2, I-C-pending) · 1× `ap1` (I-C-pending) · 1× `deftype_ctor_trailing` (frontend carry, pre-S111) · 1× `chaining_toggle_off` (increment-II reuse-token, pre-S111) · 1× R2 (vec-element-drop, /qa re-triage). **Zero genuine regressions.**

### CS-5 /review (ADVERSARIAL) — centrepiece SOUND ON ITS DECLARED SCOPE; residual FALSE-FRESH class found (pre-existing)
Independently verified: 17/17 vec-assoc COW family + nested-let/HOF/join/double-nested/multi-param probes correct; a3 genuinely 1-helper-5-sites (no 6th, Principle 7); 7 updated may-path tests correct (genuine semantics change not edited-to-pass); schema-20 round-trips (cache-hit returns correct COW value); 0634 collapse clean (no dangling refs); emission cert CONFIRMED (13/13 lane, differential-oracle + DEC_CHECK clean on 3 shapes); R2 3rd-attribution SUPPORTED (vec-element-drop). **But adversarial hunt found residuals (all PRE-EXISTING, byte-stable across CS-5, NOT regressions):**
- **B-1 (memory-safety, false-Fresh via CONTAINER-ELEMENT provenance laundering):** `(defn f [v] (vec-get [v] 0))` returned → trace-proven `result=Fresh` (the walk drops element provenance at `VecLit` construction; `vec-get`'s `ProjectionOf(0)` roots at the fresh container) → protect elided (`fn_compiler.rs:1736`) → scope-exit frees the returned alias → REPL garbage / **`--link` SIGABRT** / toggle-off GREEN (the §3.7 signature). **Falsifies the CS-5 rustdoc completeness claim** ("truthful+reachable LEAF facts sufficient" — the WALK launders provenance through containers). NOT in the 0623 matrix (no container-store axis).
- **B-2 (producer seam):** match-scrutinee var-pattern over a may-origin publishes UNCONDITIONAL `ProjectionOf(0)` — violates §3.7 reservation clause one level up from `origin_to_result_mode`. Latent under binary `==Fresh` consumers; a 2nd toggle-off-independent crash is stacked (backend, /qa attribution).
- **I-1/I-2:** adjacent pre-existing UAFs — closure captures a let-bound Vec-param alias (I-1); fresh container holding a COW-aliased element returned (I-2). Same false-Fresh/capture-provenance family.
- **I-3 (frontend wrong-reject):** renamed-import surface syntax `(source-name local-name)` (spec §8.3.5 grammar) is REJECTED by the reader → the a3 renamed-import reach path + 0621 rider are only UNIT-pinned, untestable e2e. → /qa+/dev(frontend).
- **0638 NOT CURED** (symptom shifted: double-free → macro-clause "match failed"; distinct defect, carries; /qa attribution owed).
- **S-1:** `fixpoint.rs:89 summary_of` composes the written name not `storage_fq()` — half-applies §15.2 (home is storage-derived, symbol isn't); non-load-bearing alias hygiene.

**Disposition:** /testing commits B-1/B-2/I-1/I-2 as failing-not-ignored repros (durable record). Design extension → **FIXME 0641 /design(typecheck)**: add the CONTAINER-ELEMENT provenance axis (VecLit element-store / projection-out) to the §15 model + the 0623 matrix, + correct the CS-5 rustdoc over-claim. **This false-Fresh-provenance class is a FOLLOW-UP INCREMENT** (pre-existing, new-design-sized) — the centrepiece delivered its DECLARED scope (vec-assoc COW). **SCOPE DECISION for the user: fix this residual class in-sprint (extend the centrepiece) vs carry to a follow-up ownership increment.**

**PIVOT TO CENTREPIECE (2026-07-17).** Multi-arity memory-safety area fully recorded (2 vectors fixed, B-2 carried w/ repro + I-C-coupled fix). Centrepiece CS-5 (§3.7 ownership COW-UAF) is the LEAD and has waited behind 6 carries — now prioritized. Remaining in-scope: **CS-0.5** (lane) → **CS-1.1** (0633 drop-glue re-key, in-scope memory-safety fix) → **CS-5** (schema-20 centrepiece) → **CS-6** (0604) + **0638 re-check** post-CS-5. Carried (evidence-gated, repro'd): B-2/CS-4.2 (I-C-coupled), 0638 double-free (§3.7-family, re-check post-CS-5). Pending USER: 0628, I-C.

**CS-0.5 STOPPED at the gate (/testing, nothing committed) — FIXME 0636 premise was WRONG.** The L-B1 lane (shell-script `clif_golden.sh diff` over `clif_baseline/corpus/*`+`s99/*`, NOT nextest-counted; separate from the green w0b nextest corpus) drift is TWO layers: (1) benign ctor `Type.Ctor` member-key churn (frames 07/08 pure-benign); (2) **a real behaviorally-preserving emission RESHAPE across 8 frames** (01/02/04/05/f1-f4) — RC-op/fence/call/block REDUCTIONS (f4: atomic_rmw 147→134, fence 101→86, call 233→178, blocks 733→657) = the accumulated borrow-elision + S110 keyed-consumer lowering improvements landed S104-S110, NEVER re-baselined. Behaviorally sound on the corpus (exit codes correct; s99 17/17 GREEN incl. `..._byte_identical_under_ownership_toggle`) but /testing correctly refused a blind re-baseline (per step 3 STOP — an RC-op elision needs certification as a SOUND borrow-elision, not a dropped-dec that doesn't trip here). Per-frame diffs in scratchpad.
- **PROCESS GAP found:** the L-B1 lane wasn't re-baselined as emission work landed S104-S110 (a golden-maintenance lapse; the S102 §6.2 discipline CS-5 must follow says re-baseline in the change-set that drifts). → note for /qa + close.
- **CS-0.5 re-scoped: /qa CERTIFIES the current HEAD emission sound** (differential all-Owned oracle `ownership_analysis_off` + RC-trace balance across the 13 frames — the ownership-inference.md R7 oracle) → THEN /testing re-baselines (`clif_golden.sh capture`) to the attributed known-good point → THEN CS-5's delta is clean. On the critical path to CS-5's readable re-baseline.
- **/qa VERDICT: GREEN-LIGHT (`64d68618`, PLAN §I).** 13/13 certified sound — oracle MATCH every frame, RC-balanced both polarities, DEC_CHECK 0 stale-decs. Reshape attributed to 3 LANDED INTENDED evolutions: **(1) S104 M-static spark-admission flip** (`3804e425`/`4924c26c` — the DOMINANT reduction: spark-leg deletion at non-recursive sites, symmetric thunk-RC elision NOT dropped decs), (2) S109 W1c2 `Type.Ctor` keying + S110 keyed-consumer resolver deletion, (3) S102-S107 ownership increments (non-atomic confined RC, projection elision, borrow elision). Vocab ratified (`wrong-accept`, `drop-glue-underkey`). PLAN §I.1/§I.2 rows added (multi-arity + drop-glue).
- **PROCESS FINDING (→ /testing gate, slot now):** the lane violated S102 §6.2 THREE times (S104/S109/S110) because it's shell-script-only (invisible to nextest → silent rot). **Fix: fold the lane into the nextest suite** so future emission-affecting change-sets go RED until they carry an attributed re-baseline (a Rust mirror already exists — `ownership_fences.rs::clif_golden_single_module_smoke`). Landed with the CS-0.5 re-baseline.

**CS-2 /review CLEAN (`a788b63`, no Blockers).** Deviation-flag G-F1 ruled **sound plumbing, NO /arch round-trip** (pin delegated variant choice; diagnosed error traced reaching the surface through all 5 `lift_error` sites). `assert!` promotion correct; cache-load validation complete for every slot a consumer reads today; GE-1/2 pin-exact. Findings → dispositions:
- **I-1 (Important, user-facing) → FOLD INTO CS-4 (/dev typecheck):** the `check_forms` boundary lift (`form.rs:499-509` `map_cranelisp_error` catch-all) Debug-formats `CodegenError` → the exhaustion renders as `typecheck error: CodegenError {…}` (message survives, presentation degraded — NOT the clean diagnosed error the ruling wants). Fix = explicit `CodegenError` arm preserving message/location + scope the `lift_error` gap-promotion (`form.rs:441`) to the not-found class only (CS-2 widened the class through it). **+ pin the GE-3 boundary surface** (the testing miss — GE-3 stopped at the helper, not the `check_forms` `CheckError` surface where the hole hid).
- **S-1 + S-3 → FOLD INTO CS-1.1 (/dev backend):** S-1 stale `cranelisp-backend/CLAUDE.md:48` heading ("UNCHECKED allocation" — one-word fix); S-3 retire dead shim `serialize.rs:389 read_cached_metadata` (bypasses the new validation; zero callers).
- **I-2 + S-5 → /arch** (with G-F5): `exec-flow-redefine.mmd:31` still infallible + `.svg` regen; `interfaces.md:1259` sketch + the "baselines unchanged" cascade line (backend `public-api.txt` legitimately +3 for `GotSlotOutOfRange`). At CS-5 types-landing or Phase-7.
- **S-2 → FIXME 0637 (/design backend):** `borrowed_sibling_slot` (`module.rs:2134`) is a 2nd persisted GOT index NOT covered by `callable_got_slot()`/cache-load validation — zero production readers today (no live hole), but a forward UB obligation when the borrowed-convention sibling gains a consumer.
- **S-4** (span param on the helper) low-pri → CS-4 if trivial, else drop.
- **Stage 1 DONE (`ce0124b2`).** 25 new S111 REDs + 7 prior carries; 4600/4632 pass, no genuine regression. **CW-F3a GREEN → NO /arch escalation; ownership wave cleared to proceed.** Plan reclassifications: CW-5 (if-branch) already GREEN (recognizer covers it); CW-6 (chained) RED (recognizer matches direct-source only); vec-push REPL face omitted (nondeterministic false-green avoided — `--link` face CW-7 is the guard). 0604 IR-1 did NOT fire in /testing's env (0/45) — committed as env-bound e2e w/ FIXME(/testing) (foreground write seam UNLOCATED); /sprint to run in firing env.
- **0604 CS-6 AT-RISK (2026-07-17):** the IR-1 lane also PASSED (did not fire) in the /sprint env on an isolated single run. It is an intermittent FOREGROUND concurrent-compile race — an isolated one-test run provides no concurrent-compile load, so a pass is inconclusive (the original 16/16 firing was under full-suite concurrent load). CS-6 has NO deterministic repro yet + unlocated seam. Plan: re-observe under full-suite load at CS-6; if still non-deterministic, request /qa attribution (fable-tier triage) before /dev fixes — do NOT fix a load-dependent race against a symptom-absence green (memory: verify-fix-not-symptom-absence).
- **Unit-tier rows deferred to /dev Stage 2** (per METHOD §2.2 — authored with the fix): KC-N1..N6 (R2 negatives, backend, AUTHOR-FIRST), GE-1..3 (GOT, types), CC-R/V/P matrix (CS-5), CW-S1..S3 (0621+cache), RU-1/2 (0595), QQ-B1 (frontend backstop), 0628 (HKT check-gate leak). /testing verifies presence at P5 close.

## Notes

- Baseline at S110 close: 4,590 passed / 7 known carries / 1 skipped. No source commits
  since close (git status: only cache + archive files) — baseline intact; verify at Phase-5 start.
- 4th-consecutive-audit backend items (build_isa, dispatch funnels, drop-glue, GOT) — **user ruled
  SHIP ALL** (2026-07-17); no 3rd deferral. GOT is the release-phase UB priority.

## Outcome (Phase 7)

_pending_
