# Dotted-ctor canonical keys — the COORDINATE contract for the S109 W1 keying change

**Status: WORKING (S109 Phase 3; REVISED at the W1.1a re-ruling, Phase 5).**
The binding cross-crate contract for the dotted-`Type.Ctor` keying change
(SPRINT.md bucket 2). **Archive trigger:** the W1 coordinate wave lands; the
surviving contract folds into the `type_ctor_names` rustdoc + BC §7 + the
consumer-crate rustdoc, and this file moves to `design/arch/archive/`.

**W1.1a re-ruling (user, P5): (b) COORDINATE.** `/dev`'s first landing flipped
the typecheck registration writers without the int/backend readers and without
the seeded-ctor writers — 73 regressions (measured by `/arch` re-applying the
preserved patch against the S109 baseline; classes pinned in §5). The user
ruled: canonical-real keying STAYS, and it becomes **uniform across every
constructor writer** (user `deftype`, int bootstrap seeds, typecheck test
fixtures), with **every reader** resolving through canonical-aware probes.
"100 such decisions would be chaos" — one keying rule, no seeded/user split.

What landed in Phase 3 (context): `cranelisp_types::member_key`,
`ModuleEntry::type_def_info()`, the 0567 head-visibility fix (commit
`9c69b203`). `/dev`'s W1.1a typecheck patch is preserved and substantially
correct for its scope — it is the *starting point*, not a rewrite target.

## 1. The uniform keying rule (all writers)

A **sum/enum constructor**'s real got-slotted `Def` is stored under the
canonical `member_key(Type, Ctor)` key in the type's home module; the bare
ctor name is a same-module `ModuleEntry::Import` ALIAS onto it, poisoned to
`ModuleEntry::Ambiguous` on a §8.6.5 distinct-terminal contest. A **product**
ctor (type-name == ctor-name, `type_def: Some`) keeps its single key at the
type name — no dotted key, no alias (degenerate form; spec §8.5.2).

**Writers that must apply the rule — ALL in the same change-set:**

| Writer | Site | Note |
|---|---|---|
| User `deftype` | `cranelisp-typecheck/src/adt.rs::register_constructors` | The W1.1a patch — reuse as-is |
| Typecheck fixture seeds | `cranelisp-typecheck/src/builtins.rs::register_{slist,sexp}_type` (via `register_constructors`) | Follows automatically; the fixture must mirror the LIVE shape (it exists to stand in for `bootstrap.rs`) — unit-test assertions update, not the mechanism |
| Int session seeds | `src/bootstrap.rs::register_synth_adt` (insert at ~:245) — `Option`, `Result`, `IO` (`Pure`/`Effect`), `Trace`, `TestResult`, the `macros` `SList`/`Sexp` families; `Pair` is product (unchanged) | The uniformity half the W1.1a landing missed |
| The hand-appended `IO.Bind` | `src/bootstrap.rs::register_io_type` (~:802) | Canonical `IO.Bind` + bare alias like every other sum ctor; `internal: true` rides the `Def` unchanged |

No writer may keep bare-keyed sum-ctor `Def`s. The reader-side bare fallbacks
(§3) exist for the product facet — not as license for a third keying.

## 2. Obligations A + B (unchanged, ride the same change-set)

- **A — `type_ctor_names` returns storage keys** (`cranelisp-types/src/heap.rs:269`):
  canonical `member_key` per sum ctor, the type-name key for the product facet.
  The W1.1a patch's probe-canonical-else-bare mapping is correct and, under
  uniform seeding, the bare branch serves only robustness; keep it.
- **B — `CACHE_SCHEMA_VERSION` 16 → 17** (`cranelisp-backend/src/cache/mod.rs`):
  key-meaning change in `.meta.json`. Same change-set as the writers.

## 3. The reader inventory — what W1.1a missed (empirically pinned, `/arch` P5)

Every consumer that probes a ctor `Def` by BARE key or follows aliases only
one hop. Mechanisms verified live by re-applying the preserved patch:

1. **Backend `CompileContext::lookup_constructor`**
   (`cranelisp-backend/src/compiler/context.rs:146`) — follows the import
   chain **exactly ONE hop** (:165–175) and its global fallback probes bare
   keys only. TWO failure classes from this one site:
   - *Pattern position* (`match_codegen.rs:225`): an imported bare ctor
     (`user.Nil → home.Nil-alias → home."List.Nil"`, 2 hops) misses →
     **compile error `unknown constructor: Nil`**. This single error inside
     `collections.list.test` is the ROOT of the entire prelude cascade
     (~30 regressions: `do`/`pure`/`cond`/`when`/`case`/`vec`/`list`/`def`
     all vanish because the prelude's later export lines never install).
   - *Nullary-ctor-as-value* (CLIF-verified): the tag path
     (`lookup_constructor` → `iconst tag`) misses on the 2-hop chain and
     falls through to the **fn-as-value closure wrap** over the (multi-hop
     resolvable) ctor got-fn — the value becomes a heap closure pointer, the
     match compares tags against it → **silent wrong value, runtime "match
     failed"** (`batch_cross_module_adt_export_and_pattern_match`). This is
     the soundness-shaped class: same name, two backend resolvers
     (`lookup_constructor` one-hop vs `resolve_driven` 10-hop) disagreeing.
   - **Fix (arch-ruled):** collapse `lookup_constructor` onto the ONE backend
     resolution driver (`resolution.rs::resolve_driven`, already multi-hop
     with alias substitution + child/absolute + global fallback) with a
     ctor-extracting read closure, and give the driver's qualified/global
     arms canonical-key awareness (probe `member_key` when the bare probe
     lands on a non-terminal). Do NOT widen the one-hop copy in place — it
     is the P7 divergent-duplication defect (two resolvers, one name).
2. **Int value display** (`src/display.rs::ctor_field_types` :533) — raw
   `table.get(bare_ctor)` expecting `Def{scheme}` → alias → `None` → **data
   ctors render with fields dropped** (`(Cons 2 …)` → `List.Cons`; the whole
   `display_*` class + `deftype_sum_bracketed_field_still_constructs`).
   Fix: probe `member_key(fqtn.name, ctor)` first, bare fallback (product).
3. **Int member-glob import** (`src/imports.rs::collect_member_glob` :424) —
   scans `public_symbols()` for `Def{Constructor}` matching the parent type:
   post-change it collects the CANONICAL (dotted) names but no bare aliases
   (aliases are `Import` edges, skipped) → a member-glob importer loses bare
   ctor references. Fix: for each matched canonical member also install the
   bare-alias edge (mirroring the home module's binding shape, §8.6.5
   ambiguity handling at the importer unchanged).
4. **Typecheck exhaustiveness + `instantiate_ctor` + poison diagnostics** —
   handled by the W1.1a patch (BR-1 `.`-strip, BR-2 canonical-first internal
   probe, canonical-first scheme probe, `Ambiguous` pattern arm). Keep.
5. **The staging-aware same-module alias hop** — the W1.1a patch adds
   `resolve_intra_module_alias_staging` (checker.rs) because
   `ResolutionScope`'s chain-follow reads LIVE tables for the `Import` hop,
   missing a same-cluster bare→canonical alias. **Arch ruling: fix the
   PRIMITIVE instead.** The S76 premise "beyond the first hop the walk always
   lands in other, already-committed modules" is FALSE for same-module member
   aliases (`resolve.rs::chain_follow_committed`). Amend the types-owned walk:
   when an `Import` edge's `source.module == current_module`, take the hop
   through the caller's first-hop VIEW (staging∪live) instead of the live
   table. That cures the ctor case AND the **latent field-accessor
   same-cluster bug** (§6) at the true seam; the typecheck-side fallback then
   does not land (or lands and is deleted in the same change-set).
   `cranelisp-types/src/resolve.rs` is `/arch`-owned — the W1 `/dev` makes
   this edit under this ruling (cite this section in the change-set).
6. **Int introspection/`/list`/`/search`/save** — audit-only class: sites at
   `repl.rs:2023/2725/3139`, `eval.rs:601/778`, `process_form.rs:838`,
   `redefine.rs:133` read ctor metadata off entries they already resolved
   through chain-following display paths (`resolve_entry_for_display`) — the
   S109 baseline's `search_lists_constructor_once_canonical_form` RED flips
   GREEN under the patch, and no search/introspection e2e regressed in the
   measured run. The W1 change-set AUDITS each site for raw bare-key
   `Def{Constructor}` matches (fix pattern = #2) but expects little work.
   The `/list` canonical+alias double-listing stays flagged to `/repl`
   (bucket 6 / 0572; `dotted-ctor-registration.md` §6).

## 4. Landing structure (atomicity without a mega-diff)

ONE `/dev` deployment for the coordinated change-set (typecheck + types +
backend + int) — the writers and readers of one key grammar are a single
reviewable seam (Principle 8: no landing where they disagree). Worktree
isolation is broken and the typecheck chain is serial anyway (SPRINT W1).
Internally, TWO commits in the one deployment:

- **Commit 1 — reader widening (behaviour-invariant).** All §3 readers become
  canonical-aware with bare fallback (backend driver collapse, display probe,
  member-glob, exhaustiveness/instantiate arms, the types chain-follow view
  hop). Pure widening over the CURRENT bare keying — full suite must stay at
  the S109 baseline (25 fails). This commit is independently revertable.
- **Commit 2 — writer flip + cache bump + RED flips.** All §1 writers mint
  canonical+alias; `CACHE_SCHEMA_VERSION` 17; fixture/unit assertions update;
  the dotted-ctor REDs flip. The 73-regression classes of §5 are the
  acceptance NEGATIVES: `/qa`'s plan rows for prelude-load, cross-module
  nullary match, display-with-fields, member-glob MUST be green here.

The reader-side bare fallback is NOT a Principle-8 interim: it permanently
serves the product facet (type-name key). Document per-site.

## 5. The measured regression classes (for `/qa` acceptance + the record)

Re-applied patch vs S109 baseline (4432 tests): **73 regressions / 6 RED
flips**. Classes: (A) 16 typecheck unit tests asserting bare-key storage
(fixture churn — update with the model); (B) ~30 prelude-cascade e2e (root =
§3.1 pattern-position one-hop miss in `collections.list.test`; everything
prelude-provided drops); (C) ~10 display e2e (§3.2); (D) cross-module
value/pattern e2e incl. the silent wrong-value match (§3.1 nullary class);
(E) exemplar/web/strand heavyweights (cascade of B). Full list:
`/qa` may regenerate mechanically (apply preserved patch, run, diff).

## 6. Fold-in: the latent field-accessor same-cluster `--run` defect

Surfaced by W1.1a: a bare field accessor (`v` for `Box.v`) NEVER resolved
same-cluster in `--run` (only cross-cluster REPL / cross-module were tested)
— same root as §3.5: the live-only chain-follow misses the same-module
staged alias. **Disposition: fold the FIX into W1 commit 1** (it IS §3.5's
primitive amendment) with its own failing tests FIRST per METHOD §2.2 — a
types-level unit pin (staging-view alias hop) + the `/testing` e2e twin
(same-cluster `--run` bare accessor use). It is a pre-existing defect, so its
e2e goes in as a failing-not-ignored repro ahead of the wave.

## 7. Pattern position — scrutinee-directed resolution (ruling #2) is TRACTABLE

**Arch answer to the P5 contingency: YES.** `infer_match`
(`cranelisp-typecheck/src/infer.rs:906`) infers the scrutinee FIRST and
passes `scrutinee_ty` into `check_constructor_pattern` — the ordering the
rule needs is already structural (syntax-directed algorithm W), and the
`apply_subst(state, &scrutinee_ty)` idiom needed to see through
already-unified vars is used two arms below (:945). The rule:

- In `check_constructor_pattern`, when a BARE ctor name resolves `Ambiguous`
  (or misses), apply the substitution to the scrutinee type; if the head is a
  resolvable ADT (`type_def_info` answers on the head entry), probe
  `member_key(head.name, bare)` in the head's home module and accept iff the
  terminal is a ctor of that exact type. Else → the poison error listing
  canonical alternatives (the ruling's "poison only when the scrutinee type
  cannot disambiguate").
- Determinism: the answer depends only on the scrutinee's type at the
  pattern's check point (front-to-back, no fixpoint iteration, no arm-order
  sensitivity). An unannotated lambda param scrutinee is still `Var` there →
  poison-with-hint — deterministic and per the ruling. Patterns are FLAT
  (bindings are `Symbol`s, no nesting), so no recursive case exists.
- The W1.1a "inference-order fragility" was a DIFFERENT axis — staging-vs-live
  table visibility — cured at the primitive (§3.5), not an ordering problem.
- Value position stays context-free → poison on contest (one rule, two
  contexts, per the user's framing). `/spec` revises §6.2.1 accordingly;
  DC-8/DC-2 flip to expect resolution, DC-5 reframes to poison-when-unknown.

## 8. Public-API + cache impact (net, for `/review`)

- `cranelisp-types`: **zero new public items** (member_key/type_def_info
  landed; `type_ctor_names` + chain-follow amendments are in-place).
  `public-api.txt` zero-diff expected.
- `cranelisp-backend` / int: internal only (the driver collapse removes a
  private duplicate). Zero `public-api.txt` movement.
- Cache: `CACHE_SCHEMA_VERSION` 16→17 (commit 2).
- `cranelisp-typecheck`: zero public-API movement (per
  `dotted-ctor-registration.md` §7).

## 9. Read-side delegations (decoupled, unchanged from the P3 note)

- typecheck `type_def_view_of` (`checker.rs:91`) → `entry.type_def_info()`.
- int `save.rs:696 generate_types` keys on `type_def_info().is_some()` (0573).
- `member_key` sweep: `adt.rs:599`, `checker.rs:1434`, `infer.rs:235`, the
  new registration sites (all in the W1.1a patch already).
- Stale comment `src/repl.rs:728` (0567) — reword in the int-touching wave.

## 10. DC-11 Blocker cure — the `pattern_ctors` sidecar reaches codegen (ruled `/arch`, W1 review)

**The defect (review-confirmed, post-commit-2):** typecheck resolves a
scrutinee-directed bare pattern ctor canonically (`infer.rs:1016–1060`) and
records it in `MethodResolutions.pattern_ctors` — which **no backend code
consumes** (the `mono_expr.rs` crate-doc's "the backend overlays the global
`MethodResolutions` side maps" was never built). Backend
`match_codegen.rs::compile_constructor_pattern` re-resolves the SOURCE-written
bare name context-free; for a name resolvable only via scrutinee context the
probe falls to `resolve_driven`'s global fallback — a DashMap iteration in
**arbitrary order** — wrong module's same-named ctor, wrong tag, runtime
`match failed`, run-to-run nondeterminism. The two-resolvers-disagree class
one seam up from the §3.1 cure.

**Chosen cure: (a′) — sidecar consumed, transported on the mono node.**
Candidate (b) (rewrite the pattern name to `m/Type.Ctor` text) is rejected:
it re-encodes a resolved identity as a string the backend re-parses (the
exact D47 violation `pattern_ctors` exists to prevent), and a missed rewrite
silently falls back to context-free re-resolution — the bug's return path
stays open. (a′) carries the typed `FQSymbol` and makes a population miss
LOUD (Principle 18). D47's arbitration (syntactic AST untouched; resolved
data adjacent) is preserved: the sidecar stays the typecheck-stage carrier;
the CODEGEN view — resolved-stage by definition, the same transport
`resolved_call` already uses on `Var`/`Apply` — carries it to the backend.

### 10.1 Contract change — `pattern_ctors` carries the STORAGE identity

`MethodResolutions.pattern_ctors: HashMap<Span, FQSymbol>` keeps its shape;
its `symbol` becomes **the storage key under which the ctor's `Def` actually
resolved** (canonical `Type.Ctor` for sum ctors; the type-name key for the
product facet; a bare key for any legacy/hand-seeded shape) — not the bare
display name. Single mint point: `instantiate_ctor` (`infer.rs:140–180`)
already probes canonical-then-bare; it records **whichever key HIT**. All
three `check_constructor_pattern` arms populate through it — no second
writer. (`/arch` pre-approves the field's rustdoc rewording per this section.)

### 10.2 Transport — `MonoMatchArm.resolved_ctor` + unforgettable overlay

- `cranelisp-types/src/mono_expr.rs`: `MonoMatchArm` gains
  `#[serde(default)] pub resolved_ctor: Option<FQSymbol>` — `Some` for
  `Pattern::Constructor` arms (from the sidecar), `None` for
  `Wildcard`/`Var` arms.
- `MonoExpr::from_expr` gains the parameter
  `pattern_ctors: &HashMap<Span, FQSymbol>` and populates the field at the
  `Match` arm (`mono_expr.rs:383`) keyed by the CONSTRUCTOR PATTERN's own
  span (`Pattern::Constructor.span` — the same key the sidecar writers use),
  not the arm span. **Signature change, deliberately** (Principle 18): a
  codegen view cannot be built without answering the pattern-resolution
  question — a defaulting second entry point would be the silent miss
  re-opened. Callers (all in typecheck): `program.rs:266`, the
  `program.rs:1306` vicinity, `traits/monomorphise.rs:491` — each passes its
  in-hand `state.method_resolutions.pattern_ctors` (the monomorphise
  re-check runs `check` over the cloned AST, so its own CheckState's map
  carries the same spans). Typecheck fixtures + the
  `ownership/transfer/tests.rs` MonoMatchArm literals add
  `resolved_ctor: None` (non-ctor arms) or the storage FQSymbol.
- **Cache: `CACHE_SCHEMA_VERSION` 17→18** in the same change-set —
  `codegen_view: Option<MonoDefnVariant>` serializes into `.meta.json`, and
  the new field's fresh-build value (`Some` on ctor arms) ≠ the serde
  default (`None`), so a pre-change cached view would hard-error at the
  backend (the exempt-class rule does not apply).

### 10.3 Consumption — backend reads, never re-resolves

`match_codegen.rs::compile_constructor_pattern` takes the arm's
`resolved_ctor` (threaded from the `MonoExpr::Match` arm iteration — the arm
is in hand at every call site):

- `Some(fq)` → direct keyed read: `symbol_tables.get(&fq.module)` →
  `.get(fq.symbol)` → `extract_constructor(entry)` → `(fqtn, CtorMeta)` — a
  tiny `CompileContext::ctor_meta_at(&FQSymbol)` helper. No name resolution,
  no fallback, no iteration order — deterministic by construction.
  `lookup_constructor` is no longer called from pattern position.
- `None` (or a probe miss) → **hard `CodegenError`**: "pattern constructor
  '{name}' has no typecheck resolution (pattern_ctors miss)". No silent
  fallback to context-free resolution — a population gap fails loudly at
  compile time instead of mis-tagging at runtime (Principle 18). Backend
  fixtures that hand-build views populate the field.

`lookup_constructor` survives for its VALUE-position consumers (the
nullary-as-value tag path etc.), which are in-scope-guaranteed by typecheck
— scrutinee-directed names exist only in pattern position, so the global
fallback is not reachable through them there.

> **S110 W3 supersession (FIXME 0584 closed at the S110 Phase-5
> centrepiece-close pass).** `lookup_constructor` no longer survives ANYWHERE:
> the S110 W2 value seam flipped its value-position consumers onto keyed
> carrier reads, W0.b made typecheck the sole mono-view producer (synthetic
> bodies carry `resolved_ctor` populated DIRECTLY at synthesis — their
> `Span::SYNTHETIC` nodes are structurally outside span-keyed transport — and
> the lenient builder relocated to `cranelisp_types::MonoExpr::lenient_from_expr`
> with the same two REQUIRED sidecar params), and W3 deleted
> `lookup_constructor` + `resolve_driven` outright. The interim S109
> lenient/synthetic `None`-arm fallback (the W1 deviation FIXME 0584 asked
> `/arch` to ratify or replace) was retired with it — the STRICTER alternative
> was delivered structurally, so this section's "`None` → hard `CodegenError`,
> never a fallback" is now the uniform landed truth for every pattern arm
> (`match_codegen.rs::compile_constructor_pattern`). See
> `backend-keyed-consumer.md` §5 (the W3 residual ruling).

### 10.4 I-1 fold-in — sparkability ctor-exclusion set (same mirror class)

`let_if.rs::collect_module_constructors` (:32–53) yields **storage keys**
(`Maybe.Some`, product type-names; bare aliases are `Import` entries and
never match `Def{Constructor}`), while `sparkability.rs::is_worth_sparking`
(:291) compares **source-written callee names** (bare `Some`, dotted
`Maybe.Some`, FQ `m/Some`) — sum-ctor calls silently drop out of the
exclusion set (spark-heuristic noise; visible in the env-gated
`CRANELISP_SPARK_STATS` comparison mode). Fix, both sides through the ONE
grammar (`cranelisp_types::bare_member_name`, LANDED with this ruling):
`collect_module_constructors` inserts `bare_member_name(key)` per
`Def{Constructor}` storage key; `is_worth_sparking` compares
`bare_member_name(callee)`. Heuristic-only surface (spark admission), so
terminal-segment granularity is acceptable; document that on both fns.

### 10.5 Structural invariants on the silent-skip enumerators (recommended, cheap)

`context.rs::constructor_metas`'s `filter_map` and `schema.rs::ctors_of`
silently DROP a ctor whose canonical+bare probes both miss — the next keying
drift would surface as a wrong heap classification or a wrong schema, not an
error. Add on the both-probes-miss arm:
`debug_assert!(false, "ctor '{ctor}' of '{fqtn}' has no resolvable Def — keying drift")`
(release behaviour unchanged: skip). Cheap, loud-in-CI; include in the
change-set.

### 10.6 Depth guard (LANDED with this ruling, `/arch`)

`chain_follow_committed`'s same-module recursive arm now bottoms out at
`CHAIN_FOLLOW_DEPTH_LIMIT` (self-alias / a→b→a same-module cycles read as a
miss; SIGABRT-verified pin
`resolve/tests.rs::same_module_alias_cycle_is_a_miss_not_a_stack_overflow`).

### 10.7 I-2 interaction note (NOT designed here — routed `/spec`→user)

The `adt.rs:470`-vicinity defn-over-ctor-bare-alias collision arm is a
normative §8.6.4 question. The 10.1–10.3 cure does NOT interact with it:
pattern resolution stops consulting bare aliases at codegen entirely, and
the typecheck-side scrutinee probe reads canonical keys — whichever way the
collision semantics land, only bare-name VALUE visibility changes; the
`pattern_ctors` pipeline is unaffected.

### 10.8 Public-API + cache summary

- `cranelisp-types`: `MonoMatchArm.resolved_ctor` (+1 baseline line);
  `MonoExpr::from_expr` signature change (−1/+1, in-workspace consumers
  only, `/arch` pre-approved); `bare_member_name` (+1, LANDED at this
  ruling). `pattern_ctors` doc-contract update (no shape change).
- backend/int: internal only. Cache: `CACHE_SCHEMA_VERSION` 17→18.

### 10.9 `/qa` matrix additions (the tag-order class)

- **Differing-layout twins** (the decisive rows — the committed DC-11/DC-6
  greens were tag-layout coincidences): two same-named ctors with DIFFERENT
  tags AND different arities (`Maybe = None | Some x` vs `Opt2 = Some x y |
  None2`), scrutinee-directed bare `(Some x)` matched over BOTH types in one
  program, both directions asserted; repeat with the two `deftype`s in BOTH
  source orders (DashMap-iteration sensitivity is the failure mode being
  pinned); REPL + `--run` parity; the review's cross-module `xmod.cl`
  nondeterministic repro committed as the regression guard.
- **Loud-miss pin** (backend unit): a hand-built codegen view whose ctor arm
  lacks `resolved_ctor` fails with the 10.3 CodegenError, never a fallback.
- **I-1 pin** (backend unit, spark level): with a canonically-keyed table, a
  sum-ctor call is EXCLUDED by `find_sparkable_bindings`/`find_sparkable_args`
  (assert via the exclusion set, not wall-clock).
- **Warm-cache row**: a pre-18 cache is rejected wholesale (schema bump);
  a warm-18 rerun of the differing-layout twin stays green.
