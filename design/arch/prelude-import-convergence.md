# Prelude ≡ Explicit Import — the resolution convergence ruling

**Status: RULING — LANDED (ruled S108 Wave G, Phase 2/3; both §7 `/dev`
change-sets landed S108 Inc3; `/review` verified the §7 structural criterion
CLEAR — zero `_or_prelude` names, R1–R8 GREEN, `public-api.txt` regenerated).**
Post-landing amendments (S108 Inc3 close): §3.3 row 12's "alignment step" is
RETIRED as a recorded settled deviation, and the display-vs-resolution I-1
divergence it leaves is RULED — see **§3.5**; §3.4's writer census and
non-resolution-reader set corrected to as-built. The
architectural decision behind the S108 Wave-G convergence: ONE reference
lookup with the prelude fallback intrinsic, and ONE §8.6.4 definition seam
that every definition form routes through. Consumers: `/dev` narrow
(cranelisp-typecheck + the approved `cranelisp-types` change-set), then
`/dev` narrow (src/int); `/review` for the structural grep; `/qa`'s
acceptance matrix is `tests/plan/PLAN.md` §"Prelude ≡ explicit import —
resolution-site × polarity matrix" (8 committed failing-not-ignored REDs,
R1–R8; GREEN pins G1–G8 guard behaviour preservation).

Companion class ruling: `resolve-home-enumeration.md` (the display/
enumeration side of the same family; reframed onto this model). FIXME 0564
(/audit) names this convergence's shape — divergent + entry-point
duplication — as the Duplication-attribute extension; this doc is that
category's worked exemplar.

## 1. The settled model (spec-grounded; not open)

Per `spec/08-modules.md` §8.6.1–§8.6.5 and §8.8.1 (user-settled, S102 +
2026-07-04 reversal):

- The implicit prelude is **just `(import [prelude [*]])`**. A
  prelude-provided name is in a module's scope **on identical terms to an
  explicit import**.
- Whether an implementation materialises prelude bindings into each table
  or consults the prelude on an inner miss is an **implementation detail
  with ZERO semantic weight. There is no "outer scope" as a language
  concept** — only a resolution *mechanism* (§8.8.1 "a
  resolution-mechanism detail, not a normative exemption").
- Only `let`/`fn`/`match` shadow (§8.6.3). A definition over ANY name in
  scope — explicit import, export, or prelude-provided — is a §8.6.4
  **compile-time conflict**, never a shadow. No def-over-prelude tier, no
  glob exemption, no mode exemption.
- Not-loading (suppressed/selective/empty prelude, §8.8.3) is the legal
  escape hatch: the name is then not in scope and free to define.

Design documents, rustdoc, and CLAUDE.md files under this ruling say
"the prelude **fallback**" (a mechanism) — never "the outer scope" as if
it were a scoping level with its own rules. The S78 architecture
(per-module `prelude_fallback` bit; Principle 19 role-as-data) is the
retained mechanism; what is corrected is the *conceptual* framing that
grew around it — most consequentially the
`crates/cranelisp-typecheck/CLAUDE.md` rule of thumb "pick the fallback
variant for a *reference*, the non-fallback variant to decide whether a
name is *free*", which is **spec-inverted**: a name is NOT free merely
because the prelude provides it (§8.6.4). That rule of thumb produced the
S14 deftrait silent-accept.

## 2. Actors and functions (Principle 21) — the duplication census

One semantic operation — *resolve `name` from module `M`: consult `M`'s
table (staging∪live where applicable), on a miss consult the prelude's
public surface iff `M`'s fallback bit is ON, chain-follow to the terminal,
apply visibility* — implemented today as a family of per-site variants.
The census (S108 probe):

| # | Variant | Site | Shape |
|---|---|---|---|
| 1 | `resolve` (pub) | `cranelisp-types/src/resolve.rs` | the walk WITHOUT fallback — callable by mistake at any new site |
| 2 | `resolve_with_fallback` (pub) | same | the walk WITH fallback — opt-in per call (8 args incl. `fallback_on`) |
| 3 | `resolve_current_or_prelude` | `typecheck/checker.rs:961` | copy: bit-consult + `resolve_with_fallback`, projects `Resolved` |
| 4 | `probe_current_or_prelude` | `checker.rs:1519` | byte-equivalent copy of #3, projects `.entry` as `Option` |
| 5 | `resolve_entry_in_current_module` | `checker.rs:1654` | byte-equivalent copy of #4 (a live mirror pair) |
| 6 | `resolve_terminal_entry_or_prelude` | `checker.rs:1727` | projects `(entry, home)` over #7 |
| 7 | `resolve_terminal_fq_or_prelude` | `checker.rs:1751` | copy of #3, projects `Option<Resolved>` |
| 8 | `lookup_trait_decl_or_prelude` | `checker.rs:2208` (E9, landed this increment) | #6 + `TraitDecl` projection |
| 9 | `lookup_constructor_type_with_state` | `checker.rs:717` | hand-rolled two-hop + I-1 filter (dead-code-allowed chokepoint) |
| 10 | `resolve_type_expr_in_module` leaf resolver | `checker.rs:2502–2543` | hand-rolled inline copy (arbitrary root module, own retry + I-1 filter) |
| 11 | `recognize_macro_head` | `src/expander.rs:319` | int-side hand-rolled bit-consult + `resolve_with_fallback` |
| 12 | `lookup_with_prelude_fallback{,_opt}` | `src/repl.rs:679` | int display gate: hand-rolled head-probe hop + root tier |

Plus the anti-family — same-rooted lookups WITHOUT the fallback that are
mistakable for reference resolution (the RED causes):

- `lookup_type_def_with_state` (`checker.rs:642`) — used by the `impl`
  HKT-arity gate (`impl_check.rs:70`): a prelude-provided target's arity
  is silently **unvalidated** (matrix S8 / RED R1).
- `lookup_trait_decl_with_state` (`checker.rs:2184`) — grounds the
  `deftrait` duplicate check (`registry.rs:101`) and, by its documented
  rationale, the spec-inverted "may legitimately SHADOW" behaviour
  (matrix S14 / REDs R2–R3).

And the definition forms that bypass the §8.6.4 seam entirely:
`register_trait_decl` / `register_trait_method` (trait name + method
names — REDs R2/R3/R6/R7), `register_macro_in_module`
(`src/process_form/form_dispatch.rs:223` — defmacro, REDs R4/R5), and the
import-direction predicate (`src/imports.rs:559`) that classifies only
`Def`/`TypeDef` as local definitions (RED R8).

The mechanism of the recurring class (E3/E8/0558/E9 + S8/S14/S15/S16):
**the fallback is per-variant, not intrinsic, so every new resolution or
definition site can forget it.** The bit is threaded through ~93 sites;
each variant re-decides the fallback question at its own call sites.

## 3. Ruling 1 — the one lookup: `ResolutionScope`

**The fallback becomes intrinsic to the resolution *scope*, decided once
at scope construction — never at a call site.** Per Principles 18/20,
the forgettable per-call decision is made unrepresentable: there is no
public resolution entry point that takes a per-call fallback flag, and no
public fallback-less resolution entry point at all.

### 3.1 Shape and home

Lives in **`cranelisp-types/src/resolve.rs`** (the S76 fold-in home;
Principle 15 — a query over types-owned data; consumed by typecheck AND
int with zero cross-dependency, exactly like `resolve_macro_head` today).
A checker-level wrapper was rejected: it would leave int's macro/defmacro
paths either dependent on typecheck or re-implementing the walk — the
very fragmentation being cured.

```rust
// crates/cranelisp-types/src/resolve.rs  (approved public surface)
pub struct ResolutionScope<'a, C: CodeStore, L: LinkerStore> {
    // private: symbol_tables, module_aliases, first_hop: &'a View<'a, C, L>,
    // current_module: &'a ModuleFullPath, prelude: Option<&'a ModuleFullPath>,
}

impl<'a, C: CodeStore, L: LinkerStore> ResolutionScope<'a, C, L> {
    /// `prelude`: `Some(prelude_path)` iff the module's fallback bit is ON
    /// AND `current_module != prelude` (the caller-side role datum,
    /// resolved ONCE here). `None` ⇒ no fallback for this scope (a
    /// suppressed-prelude module, the prelude itself, platform sig checks).
    pub fn new(
        symbol_tables: &'a SymbolTables<C, L>,
        module_aliases: &'a ModuleAliases,
        first_hop: &'a View<'a, C, L>,
        current_module: &'a ModuleFullPath,
        prelude: Option<&'a ModuleFullPath>,
    ) -> Self;

    /// THE reference lookup. Inner (first-hop view) walk; on a
    /// not-found-class miss of an UNQUALIFIED name, prelude retry
    /// (public-terminal I-1 filter); chain-follow; §8.7.3 visibility;
    /// §8.6.6 alias substitution for qualified names. A qualified
    /// `mod/sym` NEVER takes the prelude retry (it names its module —
    /// today's behaviour, made explicit).
    pub fn resolve(&self, name: &str, span: Span) -> Result<Resolved<C>, ResolveError>;

    /// Typed projection retained on the scope (macro-head recognition).
    pub fn resolve_macro_head(&self, name: &str, span: Span)
        -> Result<Option<FQSymbol>, ResolveError>;
}
```

- The bodies of today's `resolve` + `resolve_with_fallback` become the
  private internals of `ResolutionScope::resolve` (the I-1 public-only
  prelude-terminal filter, the miss-class-only retry, the never-self-
  fallback guard, the prelude-table-absent ⇒ miss-stands rule, and the
  Principle-16 `split_qualified`/`canonical_symbol` guards all move
  inside unchanged).
- **Free `pub fn resolve` and `pub fn resolve_with_fallback` leave the
  public surface** (demoted to private internals). A caller that
  genuinely must not fall back constructs a scope with `prelude: None` —
  the decision is explicit, at construction, in one reviewable place.
- `pub fn resolve_macro_head` (free) reshapes to the scope method; its
  `Ok(None)`-for-non-macro / miss-class contract is unchanged. This
  gives macro recognition the prelude fallback through the same intrinsic
  mechanism (replacing `recognize_macro_head`'s hand-rolled retry).
- `Resolved`, `ResolveError`, `BindingProvenance`,
  `check_binding_addition`, `substitute_module_alias` are unchanged.

### 3.2 Scope constructors — where the bit is consulted

Exactly one constructor seam per surface consults the `prelude_fallback`
role datum (which itself is unchanged — Principle 19 role-as-data;
`TypeCheckEnv.prelude_fallback` / `SharedState.prelude_fallback` stay,
threaded as today):

- **typecheck**: ONE `TypeCheckEnv::scope_for(&self, module: &ModuleFullPath)
  -> ResolutionScope<…>` (+ `scope(&self, state) = scope_for(&state.current_module)`),
  subsuming `prelude_fallback_target` (which becomes its private helper
  or inlines) and the staging∪live first-hop view selection
  (`current_symbol_table(state).view()` / the `module_path`-rooted view
  the type-expr leaf resolver builds). `scope_for` is what lets variant
  #10 (arbitrary-root) collapse too. *(Landed as
  `TypeCheckEnv::scope_resolve(state, name, span)` /
  `scope_resolve_in(module_path, …)` — checker.rs:939/964: the seam
  constructs the scope AND resolves in one call; `prelude_fallback_target`
  retained as their private bit-consult helper.)*
- **int**: scope construction at the committed-view seams that resolve —
  macro recognition (`expander.rs`) and the defmacro definition gate (§4).
  The display gate does NOT construct a scope — its lookup is a genuinely
  different operation and stays hand-rolled (settled deviation, §3.5).

### 3.3 The collapse map (exact)

| Today | Becomes |
|---|---|
| `cranelisp_types::resolve` (pub) | private internal of `ResolutionScope::resolve` |
| `cranelisp_types::resolve_with_fallback` (pub) | `ResolutionScope::resolve` (the method IS the former body) |
| `cranelisp_types::resolve_macro_head` (pub free fn) | `ResolutionScope::resolve_macro_head` |
| `resolve_current_or_prelude` | deleted → `self.scope(state).resolve(name, span)` |
| `probe_current_or_prelude` | deleted → `self.scope(state).resolve(name, Span::default()).ok().map(\|r\| r.entry)` |
| `resolve_entry_in_current_module` | deleted (mirror of the above — same projection) |
| `resolve_terminal_entry_or_prelude` | deleted → `.ok().map(\|r\| (r.entry, r.home))` at sites |
| `resolve_terminal_fq_or_prelude` | deleted → `self.scope(state).resolve(..).ok()` |
| `lookup_trait_decl_or_prelude` (E9 sibling) | deleted → ONE kind-projection `resolve_trait_decl(&self, state, name)` = `scope.resolve` + `TraitDecl` match (no `_or_prelude` in the name: fallback is intrinsic, not advertised) |
| `lookup_constructor_type_with_state` | deleted → scope.resolve + `DefKind::Constructor` projection (or retired with its dead-code caller) |
| `resolve_type_expr_in_module` leaf resolver (inline copy) | rewritten over `self.scope_for(module_path).resolve(..)` |
| `lookup_type_def_with_state` | **deleted** — the HKT arity gate (`impl_check.rs:70`) resolves the impl target through the scope + `type_def_view_of` (flips R1) |
| `lookup_trait_decl_with_state` | **deleted** — its one caller splits into the §4 seam + the idempotency probe (below) |
| `recognize_macro_head` (int) | thin: construct scope (bit consulted here), call `scope.resolve_macro_head` |
| `lookup_with_prelude_fallback{,_opt}` (int display gate) | RETAINED **as-is** — a hand-rolled three-tier HEAD probe (its root-`""` special-form tier and head-entry classification are display semantics, Principle 17's explicit root probe). The originally-planned "alignment step" (tier-1/2 re-expressed over the scope) is **RETIRED as the settled end-state, not a pending TODO** — re-expression is impossible without breaking the S20/S21 byte-identity display pins, and the display-tier lookup is a genuinely DIFFERENT operation from `resolve`. See §3.5; a future sprint MUST NOT "complete" this row |

**The only legitimate fallback-less probe** is the *idempotent
re-registration check*: "does THIS module already carry this exact
declaration?" (retry-from-top re-submission, S86 D3; REPL own-redefinition).
That is a raw current-module table probe (`probe_module_entry_owned`),
named as a probe — it answers same-module identity, **not** name-freedom,
and it must never be reachable under a name that reads like reference
resolution (matrix criterion IV.5).

### 3.4 Fate of the `prelude_fallback` bit

The bit **stays** — it is the §8.8.1 per-module fact "does this module
receive the implicit prelude" (role-as-data, Principle 19, unserialized,
recomputed per session). **Writers (as-built census, corrected S108 Inc3
— the ruling's original "single writer `worker::inject_prelude_if_needed`"
was stale):** the bit has exactly TWO legitimate write sites, both
role-datum maintenance:

- `src/process_form/dependency.rs::ensure_prelude_bit` (dependency.rs:1308)
  — the single cluster-path writer, called by BOTH arms of
  `process_cluster_once` (FIXME 0516 fold-in): fresh recompute on
  Replace/batch, incremental OFF-delta on Additive/REPL.
  `inject_prelude_if_needed` (same file) **no longer writes the bit** — it
  keeps only the prelude-LOADING job on the ON path (the fallback must
  have a table to consult).
- `src/imports.rs::install_module_session_env` — the cache-restore /
  session-env reinstall path (S102 CS-D3a; callers: repl.rs watcher
  rescope, `process_form/cache_restore.rs`, `session_v4/lifecycle.rs`),
  recomputing the same §8.8.1 invariant from the restored table's
  imports/exports.

What collapses is *consultation*: `.get(module)` reads reduce to the
scope constructors (§3.2) plus the enumerable set of non-resolution
readers that genuinely need the fact itself:

- the §8.6.5 install-time distinct-terminal poison comparator
  (`src/imports.rs`);
- the display/enumeration views — the display gate
  `lookup_with_prelude_fallback{,_opt}` (§3.5), the `eval.rs`
  bare-symbol display hop (its hand-rolled sibling on the eval-result
  path, eval.rs ~566), `describe_symbol`, `prelude_implicit_names`
  (feeding `handle_imports`' "Prelude (implicit)" group AND the agent
  harvest's in-scope grains), the E8 `impls_for_type_in_view` union, and
  the index/search feeds per `resolve-home-enumeration.md`;
- typecheck's bulk reverse-scan `find_trait_method_decl`
  (`traits/dispatch.rs` — method-name → declaring `TraitDecl`, a table
  ENUMERATION unanswerable by `resolve`, which walks name → entry; its
  prelude hop carries its own I-1 `public_only` head filter).

Fallback is therefore **a property of the
resolution scope** (per-module, constructed once), not unconditional and
not a per-call opt-in.

## 3.5 The display tier — settled deviation + the I-1 divergence RULING (S108 Inc3)

### 3.5.1 The alignment step is retired (settled end-state)

§3.3 row 12 and §7 CS2 item 4 originally planned an "alignment step":
re-express `src/repl.rs::lookup_with_prelude_fallback_opt`'s tiers 1/2 over
`ResolutionScope`. That step is **impossible as written and is retired as
the settled end-state** — record, so a future sprint doesn't "complete" it:

1. `ResolutionScope::resolve` **chain-follows to the terminal** and applies
   §8.7.3 visibility; it exposes no raw-head variant. The display gate
   answers a DIFFERENT question: the raw HEAD entry **plus the module it
   resolved in** (display provenance — `resolve_entry_for_display` chains
   separately so introspection can render the re-export chain and the §8.9
   defining-module qualification), plus a root-`""` special-form tier that
   resolution never consults.
2. Re-expressing tiers 1/2 over the scope would perturb that
   `(entry, resolving_module)` shape — breaking the S20/S21 byte-identity
   display pins.

The display-tier lookup is therefore NOT a third copy of the resolve walk
(the §2 census's "hand-rolled" reading is superseded): it is a distinct
display operation that happens to share the bit. It stays hand-rolled, and
its ONLY obligation to the resolution layer is agreement on scope
membership — which is exactly where the one residual divergence sat (§3.5.2).

### 3.5.2 The I-1 divergence — RULED: a defect (display applies the same filter)

**The divergence.** `ResolutionScope::resolve`'s prelude retry applies the
I-1 public-only filter (a private prelude binding does NOT leak as a bare
name). The display-tier prelude hop does not: `lookup_with_prelude_fallback_opt`
(repl.rs ~720) and the `eval.rs` bare-symbol display hop (~566) take the
prelude HEAD with **no** `is_public()` check. So a PRIVATE prelude binding
classifies as "in scope" for display — the bare-name/introspection display,
`/search`'s "already in scope — no import needed" mark
(`is_already_in_scope` / `exact_in_scope_hit`), and the agent harvest's
mentionable gate (`symbol_is_mentionable`) — while resolution correctly
rejects it. Post-convergence this is the only place the two answers can
disagree. Pre-existing, display-only.

**Ruling: BUG — display MUST apply the same public-only filter.** Grounds
(spec, not taste — no user escalation needed, §8.8.1's MUST already decides
it):

- §8.8.1 obliges the implementation to make "the prelude's **public**
  names" available; the fallback resolves "against the `prelude` module's
  **public** bindings". A private prelude binding is NOT in the module's
  scope — not resolvable, not importable, not bindable (§8.7.3, §8.6.4).
- Classifying it "in scope" is therefore a false scope statement, worst at
  `/search`: "already in scope — no import needed" for a name no reference
  can actually resolve (the self-documenting-REPL principle requires
  feedback to reflect what the language will do).
- Every OTHER display/enumeration prelude reader already applies the
  filter — `prelude_implicit_names` (`is_public`), the E8
  `impls_for_type_in_view` post-filter, `find_trait_method_decl`'s
  `public_only` hop, `recognize_macro_head`'s post-filter. The two
  unfiltered sites are drift, not design.

**The `/dev` fix (narrow, src/int; behaviour-invariant for the stock
prelude, a pure re-export shell whose heads are all public):**

- `src/repl.rs::lookup_with_prelude_fallback_opt` — the prelude tier's hit
  requires the prelude HEAD entry `is_public()`; a private head falls
  through (root tier / `None`). All divergent classifiers inherit through
  this one gate (`describe_symbol`, `resolve_entry_arg`,
  `is_already_in_scope`, `exact_in_scope_hit`, `symbol_is_bound` tier-1,
  agent-harvest `symbol_is_mentionable` tier-1).
- `src/eval.rs` bare-symbol display hop (~566–583) — the same head filter
  on the prelude-table hit.
- Unit tests at BOTH seams (a private prelude entry is not classified
  in-scope / not displayed) per METHOD §2.2; e2e warranted (observable
  end-to-end): under a fixture prelude with a `defn-`/private binding,
  bare `<name>` takes the unknown-symbol path and `/search <name>` never
  prints the in-scope mark.

**Residual RESOLVED (types-side, `/arch` — was FIXME 0567; fixed S109
Phase 3).** Resolution's I-1 filter tested the chain-followed TERMINAL's
visibility (`resolve_with_prelude`), not the prelude HEAD's — a PRIVATE
`(import …)` edge inside the prelude chaining to a PUBLIC terminal leaked
through `resolve` while the head-filtered display hid it (the mirror-image
divergence; unreachable through the stock prelude, which carries no private
imports). §8.8.1's "prelude's public names" reads as head (binding)
visibility, so the retry now gates on the prelude head entry's
`is_public()` with the terminal check kept as defence in depth — display
and resolution agree on the head reading. Failing-unit-pin-first per METHOD
§2.2: `cranelisp-types/src/resolve/tests.rs::
scope_i1_filter_gates_on_prelude_head_not_terminal` (+ the
public-reexport-edge complement pinning stock-prelude invariance). Zero
public-API delta; no cache impact.

## 4. Ruling 2 — the one definition seam

**Every definition form routes through ONE §8.6.4 seam, and that seam
consults the prelude — to REJECT, per §8.6.4.** The GREEN target shape
already exists: `reject_def_over_binding` (checker.rs:1013; 33/33 green
for `defn`/`defn-`/`deftype`). It is generalised, not multiplied:

### 4.1 The seam moves one level down (multi-consumer)

The glue — synthetic-name guard (`$` / `__` prefixed names skip),
resolve-in-scope, provenance classification (home == current ⇒
`Definition`/allowed; inner `Import` head ⇒ `Import`/`Export` by
visibility; otherwise ⇒ `Prelude`), delegate to `check_binding_addition`
— relocates to **`cranelisp-types/src/resolve.rs`** beside
`check_binding_addition`:

```rust
pub fn reject_def_over_binding<C: CodeStore, L: LinkerStore>(
    scope: &ResolutionScope<'_, C, L>,
    name: &Symbol,
    span: Span,
) -> Result<(), CranelispError>;
```

Grounds: the rule already has ONE predicate (`check_binding_addition`,
FIXME 0516); what was still per-surface was the resolve+classify glue —
and the defmacro path lives in **int**, which must call the identical
seam without a typecheck dependency (the same multi-consumer argument
that placed the resolution primitive here). Typecheck's
`reject_def_over_binding` method becomes a 3-line adapter
(`cranelisp_types::reject_def_over_binding(&self.scope(state), name, span)`).

The seam consults **module scope only** (inner table ∪ prelude fallback).
It never consults the root `""` module — root special forms are reserved
by a different rule (Principle 10), and today's stdlib `do` macro over
the root special form remains out of this seam's jurisdiction (unchanged
behaviour; the `resolve` walk never reaches root).

### 4.2 Routing — which forms hit the seam where

| Definition form | Seam site | Status |
|---|---|---|
| `defn` / `defn-` (single + multi-sig) | `program.rs` `check_form_register` `Defn` arm (existing) | GREEN today (S12) |
| `deftype` | `check_form_register` `TypeDef` arm (existing) | GREEN today (S13) |
| **`deftrait` / `deftrait-` — trait NAME** | `check_form_register` `TraitDecl` arm gains the seam call BEFORE `register_trait_decl` | flips **R2, R3** |
| **`deftrait` — each METHOD name** | same arm: loop `decl.methods`, seam per method name — placed at the arm (not inside `register_trait_decl`) so it covers the plain AND HKT registration branches with one call site, and `check_form_register` remains the ONE visible place all typecheck-side definition forms hit the seam | flips **R6, R7** |
| **`defmacro` / `defmacro-`** | int: `register_macro_in_module` (`form_dispatch.rs`) gains a gate at the top — construct the int scope (committed view + bit + aliases) → the types seam. Mode-uniform by construction (it sits in the shared structural peel) | flips **R4, R5** |
| **import/export over a local definition** (symmetric direction) | `src/imports.rs:559`: widen the local-definition classification to `Def` (already covers `DefKind::Macro` Defs) **∪ `TypeDef` ∪ `TraitDecl`**; diagnose the R8-macro RED with the committed test and fix at THIS seam (no new parallel check) | flips **R8** pair |

Interaction with the `deftrait` duplicate check (`registry.rs:101`): the
seam runs FIRST at the arm. A prelude/import-provided contest errors
there (with the §8.6.4 conflict diagnostic + FQ remedy — which also
upgrades the R2 explicit-arm wording from `trait Show already defined`,
the PLAN's ride-along SHOULD). What remains inside `register_trait_decl`
is only the same-module question, re-expressed per §3.3 as the raw
idempotency probe: identical re-submission ⇒ no-op; genuinely different
same-module redecl ⇒ `trait X already defined` (spec §7.1). The
retry-from-top contract (S86 D3) is preserved: on re-submission every
seam resolve lands home == current ⇒ `Definition` provenance ⇒ allowed.

### 4.3 The named correction for `/dev` (typecheck CLAUDE.md)

`crates/cranelisp-typecheck/CLAUDE.md` §"Bare-name resolution &
the implicit-prelude OUTER SCOPE" MUST be corrected in the same
change-set (it is `/dev`-owned; this ruling is the instruction):

- **Delete** the `lookup_trait_decl_or_prelude` bullet's rationale
  sentences claiming the `deftrait` duplicate-check "relies on NOT
  seeing a prelude decl, so a user `(deftrait Display …)` may
  legitimately SHADOW a prelude-globbed one", and the rule of thumb
  "Pick the fallback variant for a *reference* …, the non-fallback
  variant to decide whether a name is *free*". Both are spec-inverted
  (§8.6.4: a binding must consult the prelude — to reject).
- **Replace** with: exactly two semantic operations exist and BOTH
  consult the prelude — *resolve-a-reference* (`ResolutionScope::resolve`,
  fallback intrinsic) and *may-this-name-be-defined* (the §8.6.4 seam,
  derived from the same resolve; home == current ⇒ redefinition allowed).
  The only current-module-only probe is the idempotent re-registration
  check, which answers a different question (same-module identity, not
  name-freedom).
- Retitle the section off "OUTER SCOPE" onto the fallback-mechanism
  framing (§1 above), and replace the chokepoint-family enumeration with
  the single scope constructor.

## 5. Blast radius (scouted 2026-07-12, concrete)

The new rejections are: deftrait-name, deftrait-method-name, and
defmacro-name over an in-scope name (both prelude and explicit-import
arms), the symmetric import-over-local-{trait,macro}, and the R1 HKT
arity validation of prelude-provided impl targets. (`defn`/`deftype`
arms are already enforced and green.) Scout results:

- **stdlib: NO self-collision.** `stdlib/prelude.cl` is a pure re-export
  shell (zero definitions). Every definition-bearing stdlib module
  already practices §8.6.4 hygiene — `(import [prelude []])` (or another
  prelude reference) suppresses the implicit glob in ALL of: `control.cl`,
  `defs.cl`, `derive.cl`, `default.cl`, `num.cl` + `num/*`, `compare/*`,
  `text/*`, `fn/*`, `io/monad.cl`, `collections/*`, `core/*`,
  `testing/*`. The only non-suppressing stdlib files are the `*/test.cl`
  submodules (define only `test-*` fns — no deftrait/defmacro) and
  `prelude.cl` itself (never self-falls-back). The compiler will still
  build its own prelude and stdlib.
- **Self-re-export is safe by construction**: a module defining `X` that
  the prelude re-exports FROM THAT MODULE resolves home == current ⇒
  `Definition` provenance ⇒ allowed. No stdlib module trips its own
  re-export.
- **examples/: clean.** `examples/lib/prelude.cl` re-exports only
  primitives (types + kebab-case fns + `not`); the examples' own
  `deftrait Num/Eq/Ord/Display` + `defmacro when/unless/->/->>` collide
  with none of them (verified name-by-name; no example deftrait method
  named `not` or any primitive name).
- **exemplar/: clean.** No `deftrait`/`defmacro` in exemplar sources; its
  `defn`/`deftype` surface is already under the enforced green arms.
- **Committed test corpus: no GREEN test found relying on the silent
  accepts.** The three collision-shaped candidates all sit under
  non-providing preludes: `spec_08_modules.rs` eqmod `deftrait Eq`
  (no prelude fixture), `repl_watch.rs` `deftrait Num` (defined IN the
  test's own prelude.cl — never self-falls-back),
  `repl_introspection.rs` `defmacro cond` + `deftrait (Display a)` /
  `Showable (show …)` (PrimitivesOnly — provides neither `cond`, `show`,
  nor `Display`). `regression.rs`'s 9× `deftype Option` are under the
  already-enforced deftype arm and pass today, so their preludes don't
  provide `Option`. Residual risk — an unscouted method-name contest
  against `TestStandard`'s `(export [primitives [*]])` glob — is
  bounded by the kebab-case primitive namespace and settled definitively
  by the full-suite run in the /dev change-set.
- **R1 arity gate:** no stdlib/examples HKT trait has a prelude-provided
  impl target (stdlib HKT traits: none in the prelude graph; examples
  define `Functor` + targets locally).

**Verdict: small. No stdlib FIXME, no user escalation, no design tension
— the stdlib already conforms. S108-completable** (two serial /dev
change-sets, §7). If the full-suite run surfaces a handful of
`TestStandard` method-name contests, they are test-fixture hygiene
(rename or suppress), routed to `/testing` in the same wave — not a
reason to split the sprint.

## 6. Public-API and cache verdict

**`cranelisp-types` public surface (approved diff — this section is the
/arch approval; `/dev` lands it WITH the typecheck consumer collapse in
ONE change-set, regenerating `crates/cranelisp-types/public-api.txt`, per
the S102 CS-A carrier precedent and the baseline-diff discipline):**

- ADDED: `ResolutionScope` (+ `new`, `resolve`, `resolve_macro_head`) and
  `reject_def_over_binding` (free fn, §4.1). `#[non_exhaustive]` policy
  does not apply (`View`-precedent private-fields struct).
- REMOVED: free `pub fn resolve`, `pub fn resolve_with_fallback`,
  free-fn form of `pub fn resolve_macro_head`.
- UNCHANGED: `Resolved`, `ResolveError`, `BindingProvenance`,
  `check_binding_addition`, `substitute_module_alias`.

Narrative record: `design/arch/interfaces.md` §"Resolution primitive"
(updated with this ruling). `interfaces.md`'s prior §"resolve_with_fallback"
section is superseded by the scope shape.

**Cache: NO impact, NO `CACHE_SCHEMA_VERSION` bump.** No serde-visible
type changes; `ResolutionScope` is a borrow-carrying view, never
serialized; `prelude_fallback` remains session-side/unserialized;
resolution results are not cached — resolution runs live against the
mounted tables. Making the fallback intrinsic changes no cached bytes.
Residue (accepted, general to any semantic tightening): a module cached
by an older compiler whose source contains a now-rejected collision is
re-checked only when its source hash changes; the new rejections fire on
fresh checks, which is what the mode-parity RED (R3) exercises.

## 7. `/dev` implementation plan (ordered; serial; one agent tests) — EXECUTED (S108 Inc3)

**Change-set 1 — `/dev` narrow (typecheck + the approved types diff):**

1. `cranelisp-types/src/resolve.rs`: introduce `ResolutionScope` per
   §3.1 (absorb `resolve` + `resolve_with_fallback` bodies; add the
   explicit qualified-name-never-retries guard; move `resolve_macro_head`
   onto the scope); add types-level `reject_def_over_binding` per §4.1
   (relocating the checker glue: synthetic-name guard, provenance
   classification off the scope's first-hop head, `check_binding_addition`
   delegate). Demote the free fns. Update `lib.rs` re-exports; regenerate
   `public-api.txt`; unit tests move/extend beside (`resolve/tests.rs`):
   fallback-intrinsic scenarios, I-1 private-prelude filter, qualified
   no-retry, seam provenance matrix {Definition, Import, Export, Prelude}
   × {allowed, rejected} (Principle 23 scenario classes).
2. `typecheck/checker.rs`: add `scope_for`/`scope` (§3.2 — the ONE bit
   consult + view selection). Execute the §3.3 collapse map: delete
   variants #3–#10 + `lookup_trait_decl_with_state` +
   `lookup_type_def_with_state`; re-point call sites (~40) with inline
   projections; keep only kind-projection helpers with non-`_or_prelude`
   names (`resolve_trait_decl`). `reject_def_over_binding` method becomes
   the adapter. `test_support.rs` fixture accessors follow.
3. `typecheck/program.rs` `check_form_register` `TraitDecl` arm: seam for
   the trait name + each method name (§4.2). R2/R3/R6/R7 flip.
4. `typecheck/traits/registry.rs` `register_trait_decl`: duplicate check
   re-expressed as the raw same-module idempotency probe (§3.3/§4.2),
   commented as such.
5. `typecheck/traits/impl_check.rs:70`: HKT arity gate resolves the
   target through the scope + `type_def_view_of` (reuse the fn's own
   `fq_impl_type` resolution where possible — resolve once, Principle 7).
   R1 flips.
6. Correct `crates/cranelisp-typecheck/CLAUDE.md` per §4.3.
7. Unit tests per METHOD §2.2 at each touched seam; then the full suite:
   expect R1, R2, R3, R6, R7 GREEN; R4, R5, R8 still RED; all 33
   `spec_08_name_shadowing` controls + G-pins + S1–S21 GREEN rows
   unchanged.

**Change-set 2 — `/dev` narrow (src/int):**

1. `src/process_form/form_dispatch.rs::register_macro_in_module`: the
   defmacro gate (§4.2) — construct the int scope (committed view;
   `SharedState.prelude_fallback`-derived `prelude` arg; aliases) →
   `cranelisp_types::reject_def_over_binding`; rejected form has no
   effect (error through the normal form-error path). R4/R5 flip.
2. `src/expander.rs::recognize_macro_head`: mechanical re-expression over
   the scope (behaviour identical; its own retry + public filter delete).
3. `src/imports.rs`: widen the local-definition arm to include
   `TraitDecl` (and diagnose the committed R8-macro RED at this seam —
   the fix lands here, not as a parallel check). R8 pair flips.
4. ~~Alignment (non-blocking): `src/repl.rs::lookup_with_prelude_fallback_opt`
   tier-1/2 over the scope~~ — **RETIRED, settled deviation (§3.5.1)**: the
   scope exposes no raw-head variant and re-expression would break the
   S20/S21 byte-identity pins; the display gate stays hand-rolled. The I-1
   filter it consequently lacks is ruled a separate defect (§3.5.2).
5. Doc correction (int-owned, same change-set): retitle `src/CLAUDE.md`
   §"Prelude as an OUTER SCOPE (not flattened)" onto the fallback-mechanism
   framing (§1) — the mechanism description underneath is accurate and
   stays; only the concept-level "outer scope" heading/wording corrects.
6. Full suite: all 8 REDs GREEN; zero regressions among the G-pins and
   the 33-green shadowing matrix.

**`/review` structural acceptance** (matrix §IV):
`grep -rn "_or_prelude\|prelude_fallback" crates/ src/` post-state —
**zero `_or_prelude` names anywhere**; `prelude_fallback` hits reduce to:
the role datum's definition + threading (`TypeCheckEnv`/`SharedState`,
`check_forms` param), the scope constructors (§3.2), the §3.4 enumerated
non-resolution readers, and tests. Any new hit outside that set is a
finding.

## 8. Sprint verdict and linkage

- **S108-completable** (§5): two serial /dev change-sets against a
  committed RED/GREEN acceptance matrix; blast radius scouted small; no
  cross-skill dependency beyond the already-filed matrix.
- **FIXME 0564** (`target: /audit`) stays open and untouched; this doc is
  the worked exemplar its facets 2 (divergent duplication — census §2
  rows 3–12) and 3 (entry-point duplication — §4.2's per-form seam
  bypasses) name. FIXME 0565 (`/review` cue) pairs on the per-diff side.
- **FIXME 0563** (`target: /arch`, resolve-home-enumeration §4 lifecycle
  gaps) was adjacent but independent — actioned and deleted at S108 Inc3
  close (the §4 amendments landed in `resolve-home-enumeration.md`).
- **FIXME 0567** (`target: /arch`, the §3.5.2 residual — resolve's
  terminal-vs-head I-1 filter) — actioned and deleted S109 Phase 3 (head
  filter landed with unit pins; see §3.5.2).

## Next skills

- `/dev` (typecheck+types) → `/dev` (src/int), serial, per §7.
- `/review` (typecheck, then int) — change-set review incl. the §7 grep
  and the public-api baseline diff.
- `/qa` — matrix upkeep as rows flip; the §V stale-framing cleanup rides
  `/testing`'s wave.
