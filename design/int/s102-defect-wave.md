> **HISTORICAL — superseded slice / working doc (triaged S110, FIXME 0607).** A
> point-in-time implementation-slice narrative, retained for the audit trail only; NOT
> current design intent. The durable design is `int.md` (master) plus the subsystem docs
> indexed in `design/int/CLAUDE.md` §"Document index". Where this doc disagrees with the
> current source or the master, the source and master win.

# S102 defect wave — /int-owned cluster designs (Block A items 1, 2, 4, 5)

> **Status: DESIGN (S102 Phase 3).** Companion to `design/int/session-transaction.md`
> (amended this phase: §9.1.1 downgrade `stale:` contract; §10 T1 full-cure mechanics).
> Scope authority: `sprints/SPRINT.md` Block A. Acceptance authority: the S101 6a/6b
> guard set (`tests/plan/ledger.md` §"Sprint 101 Phase 6a/6b defect set") — every design
> below names the guards it flips. Master design: `design/int/int.md` (§8 REPL flow,
> §8.3 regeneration, §8.6 transaction).
>
> Normative UX inputs: `repl/spec.md` §18.1.1 (downgrade report — /repl landed the
> wording this phase), §18.5 (trap presentation), §18.8 (restart floor), §14.4
> (error-blocked state), §15.4 (regeneration invariants, authorship fidelity), §3.6
> (/info source). Where /repl or /spec work is still in flight (0484 precedence,
> 0492 arbitration), the design is conditional and says so.

---

## §1. T1 interim cure — the downgrade print (ships regardless)

**Ruling-grade content lives in `session-transaction.md`** (§9.1.1 data contract, §10 T1
amendment); this section is the change-set plan.

Mechanism recap: the §2.2 `!per_symbol` classification arm (prior `Def` exists, target
kind outside concrete-single-sig precision, not gate-exempt) is the T1 route. The turn
gains the `repl/spec.md` §18.1.1 `stale:` section: header line
`; stale: compiled callers keep the previous definition of {cause}` + §1.1-layout caller
names. The **trigger is the route, not the surface diff** — even a scheme-equal
redefinition of a polymorphic template leaves previously-minted mono instances (and their
compiled callers) stale. The **set** is the direct reverse-edge callers of the target and
its `$`-mangled variants, restricted to compiled (`code: Some`) entries, excluding
`is_gate_exempt_internal` names; omitted entirely when empty (§18.1.1 negative half:
never-compiled/late-bound callers MUST NOT appear).

**Change-set plan (one change-set, small):**

1. `src/redefine.rs` — `TransactionReport` gains `stale: Vec<FQSymbol>`; `render` gains
   the `; stale:` section (header exact per §18.1.1; same name-layout closure as the
   existing sections). New pure fn `stale_callers(tables, target) -> Vec<FQSymbol>`:
   `ReverseIndex::build` + `callers_of(target) ∪ callers_of(target$…)` (variant-aware:
   a mangled callee whose `base_fq` == target), filtered to entries with compiled code,
   `is_gate_exempt_internal` excluded, sorted/deduped.
2. `src/redefine.rs::apply_redefinition_outcomes` — a second arm: for outcomes
   matching the item-3 trigger (`prior_was_def && !per_symbol`, gate-exempt excluded),
   build the stale set; if non-empty, push a `TransactionReport { target, stale, .. }`
   rendering through the existing `pending_cascade_reports` channel (Principle 8 pin:
   the full cure keeps this section, rendered empty).
3. `src/worker.rs::commit_staging_to_live` — widen `RedefinitionOutcome` production.
   **Verified as-built (S102 Phase-3 trace): the single `outcomes.push` sits inside the
   `entry.callable_got_slot().is_some()` arm (`worker.rs:571`), so BOTH T1 shapes emit
   no outcome today** — (a) slot-less staged displacing a slotted prior (the FIXME-0479
   `else if` displacement arm, `worker.rs:581–612`, retains code but pushes nothing) and
   (b) template-replacing-template (slot-less over slot-less prior `Def`, which falls
   straight to `live.insert` — and whose classification arm returns `(New, false)` for a
   slot-less prior, conflating "genuinely new" with "template redefinition"). Change:
   `RedefinitionOutcome` gains `prior_was_def: bool`; the gate emits an outcome for
   every staged `Def` whose name had a prior live `Def` (any slot shape, both arms +
   the fall-through). The print triggers on
   `prior_was_def && !per_symbol && !is_gate_exempt_internal(name)` — never on genuine
   `New` (no prior `Def`, incl. the prior-`Import` shadow shape, which is 0484's
   territory, not a downgrade).
4. Unit scenarios (Matrix C below, per METHOD §2.2 / Principle 23): route-trigger cells
   (concrete→poly, poly→poly same-scheme, poly→poly changed, concrete→overloaded,
   macro/ctor targets), set-exactness cells (compiled caller in / template caller out /
   `__expr` out / cross-module caller qualified), empty-set omission, and the negative
   "concrete AbiChanging target never produces stale" (mutual exclusion with the
   transaction).
5. E2E: the §18.1.1 requirement rows are `[S102]`-tagged with no guards yet — /qa's
   L-U1 lane (unannotated-default siblings) is the carrier; the worked `id`/`g`
   transcript in §18.1.1 is the canonical script.

Dependencies: none on /spec; /repl's §18.1.1 wording is already landed (this design
binds to it). No cross-crate change; no `cranelisp-types` change.

## §2. T1 full cure — sizing verdict

> **S103 UPDATE (FIXME 0507, /design src/): PROMOTED to implementation-ready.** The S102
> preconditions named below (D1/D2 regen fidelity, the 0489 floor, D3/0487 env) all landed at
> S102, so the deferral condition is discharged. The implementation-ready change-sets (CS-1
> end-of-turn driver, CS-2 report integration, CS-3 edges) + the F2 slot-refined trigger + the
> F5a macro-target handling + the F3 macro-clause resolution now live in
> `session-transaction.md §10 T1` (the authoritative home). The §5.2 `error_modules` framing
> below is corrected per 0507 addendum 5: the §14.4 gate WAS wired in `process_commands`; the
> Wave-5 change was the §18.8 definition carve-out (`is_repair_definition_turn`).

**VERDICT (as of S102): OUT of S102 — defer to S103, with the print as shipped mitigation.**
Mechanics are designed (session-transaction.md §10 T1 amendment: end-of-turn reload
after `regenerate_backing_file`, watcher-discipline `reload_module` + `poll_and_reload`
dependents cascade, all through the §7.3 Replace gate). The honest sizing:

- **Mechanically moderate, not large**: ~3 change-sets on `src/` — (a) the end-of-turn
  driver (eval path: after regen, reload target module + dependents,
  eval-synchronous); (b) report integration (module-grain reload outcomes rendered
  through the §9.1 channel — needs a /repl wording increment for module-grain
  reporting); (c) edge handling (reload failure → §14.4 error-blocked, never lockout;
  `should_regenerate`-suppressed modules keep the `stale:` print).
- **But it sits BEHIND this sprint's own Block A2/A4 fixes as hard preconditions**:
  the reload's input is the regenerated backing file, so D1 (expansion-artifact
  double-persist → reload dies at `defmacro name must be a symbol`), D2 (authorship
  re-render → reload silently rewrites the user's source semantics), and 0489 (a
  failed reload must not strand the session) must all be landed and settled first —
  and D3/0487's cache-restore env fix determines whether a reloaded file-backed
  module recompiles at all. Landing the full cure in the same sprint means stacking
  it on top of freshly-changed lifecycle/save seams with no soak, in a sprint whose
  spine (Block B) already carries the close-short risk.
- **Cost profile note**: the cure makes every T1 redefinition turn a module reload +
  dependent-module cascade (whole-module recompiles). Acceptable for the dev loop it
  serves, but it deserves its own turn-latency look (L-D1 protects only the concrete
  body-only path) — another reason not to rush it into the tail of S102.

**What S102 must leave in place for S103** (all already scoped in-sprint):
faithful regeneration (D1/D2 cures — §4), the 0489 prompt floor + §14.4 degrade path
(§5), the D3/0487 cache-restore env recompute (§6), and the `stale:` print worded as a
kept transaction-report section (§1 — the arch Principle-8 pin). Increment I (Block B)
needs nothing extra: the §2.4 `AbiSurface` seam is untouched by the reload driver, and
mode-vector widening at the seam only sharpens the same gate both granularities share.
No increment-I mechanism writes to the lifecycle/save seams the cure consumes.

Suggested S103 shape: one wave — driver + /repl module-grain report wording + flip of
the two coherent-stale pinning tests (`redefine_concrete_to_polymorphic_caller_…` /
`…_overloaded_…` carry flip notes) + an L-U1 extension asserting the `stale:` section
renders empty under the cure.

---

## §3. Scenario-space matrices (Principle 23 — named here, drained by FIXME 0496)

The /int defect wave touches four strategy seams. Their scenario spaces, named
explicitly — FIXME 0496's unit briefs derive from these matrices; /qa's L-S2/L-S3
lanes are the e2e complement. Cells marked ✗ are the S101 defect cells.

**Matrix A — session lifecycle (`lifecycle.rs` restore/startup decision paths; L-S2)**

| Session-start state × | first turn: expr-only | def | defmacro | macro-defining-macro use | redef (body) | redef (sig) | /mod M def |
|---|---|---|---|---|---|---|---|
| fresh dir (no backing, no cache) | | | | ✗ D1 | | | |
| backing green, no cache | | | | | | | |
| backing green + cache (restore) | | | | | | ✗ D3 | ✗ D3/0487 |
| backing BROKEN (post-§18.4 quit) | ✗ 0489 (never reaches a prompt at all) | ✗ 0489 repair turn | | | | | |
| hand-authored batch `user.cl` (adoption) | ✓ control (no rewrite) | ✗ D2 (re-render) | | | | | |
| `--no-cache` × each of the above | ✗ D1 (doesn't recover) | | | | | | |

Observations per cell: reaches-prompt?, backing-file bytes (faithful / untouched /
appended-only), cache write vs poison, error-set state, introspection state.

**Matrix B — regeneration grammar (`save.rs::generate_module_source`; feeds §4)**

Entry-kind axis {defn, def-value, deftype, deftrait, impl, defmacro (user-authored),
defmacro (macro-expansion artifact — D1's poison cell), import, export, `(mod)` bare,
`(mod)` inline-body (0343 suppression), platform decl, module preamble} ×
provenance axis {REPL-authored this session, file-originated hand-authored text,
cache-restored + rehydrated, expansion product of an earlier turn} ×
assertions {round-trips (reload reproduces session state — §15.1), authorship fidelity
(original text preserved byte-wise — §15.4.7), single-authority (never both an
expansion artifact AND its originating form — D1)}.

**Matrix C — redefinition target-kind × artifact world (`redefine.rs`; feeds §1)**

Target kind {concrete UserFn, generalized/polymorphic template, overloaded base, macro,
ctor/deftype, trait impl} × surface {scheme-equal, scheme-changed} × caller world
{none, compiled concrete caller, minted mono instances, closure/partial captures,
`__expr` wrapper} × expected channel {per-symbol transaction / `stale:` print / nothing}.

**Matrix D — module-turn environment (`/mod M` + transaction re-check env; feeds §6; L-S3)**

Module provenance {entry, file-backed fresh-compiled, file-backed cache-restored,
`/mod`-created blank} × env dimension {prelude values (fallback bit), prelude type
aliases, module aliases, own imports, introspection/typecheck_products presence} ×
consumer {interactive `/mod M` turn, transaction SCC re-check (§4.2), rehydration
(`resolve_recheck_sexps`), introspection commands}.

**Matrix E — introspection recording (the `eval.rs:130–146` writer + the
`process_form.rs:610–645` / `form_dispatch.rs:255–266` writers; feeds §7.3 0486 and
§4's D1 recording rules)**

Turn kind {defn, redefinition, bare lookup (healthy / broken symbol), call expression,
expression via `__expr`, macro-expansion-produced defn, slash command} × effect
{creates record, updates source+sexp with the AUTHORED text, MUST NOT touch existing
record}.

---

## §4. Persistence-integrity cluster — D1 + D2 (regeneration fidelity)

### 4.1 Root causes (source-verified, S102 Phase-3 trace)

**D1 — expansion-artifact/origin double-persist.** Two introspection-recording sites
disagree about which sexp is the regeneration authority for a macro-expansion-produced
definition:

- the built-defn loop keys **every** defn of the turn to the turn's ORIGINAL outer form
  (`process_form.rs:629` — `entry.sexp = Some(sexp.clone())` where `sexp` is the
  `process_regular_form` param, i.e. `(mdef x 1)`); the expanded form rides `.expanded`;
- the defmacro-registration path stores the **EXPANDED** `(defmacro x …)` artifact
  (`form_dispatch.rs:261` + `macro_sexp`, `form_dispatch.rs:288`).

`save::generate_module_source` (§8 section, `save.rs:606–692`) then emits both: the
expanded `(defmacro x …)` (from `x`'s record/`macro_sexp`) AND `(mdef x 1)` (recorded as
`x-def`'s sexp) — which do not co-load: at restart the original re-expands while `x` is
already a macro → `defmacro name must be a symbol`, exit 1 pre-prompt, `--no-cache`
powerless (the poison is the source file).

**D2 — authorship re-render.** Regeneration renders every definition from its parsed
`Sexp` (`render_decl_sexp`, `save.rs:192`), never from the verbatim
`Introspection.source` text; `Sexp` has no quote/quasiquote variants (reader desugars,
`reader.rs:870–913`), so an adopted hand-authored `` `(add-i64 ~e ~e) `` regenerates as
`(quasiquote (add-i64 (unquote e) (unquote e)))`. The rehydration path compounds it:
`rehydrate_userfn_introspection_from_source` sets `source = pretty_print(sexp)`
(`save.rs:787–789`) even though it is holding the original file text at that moment.

### 4.2 The cure — one authorship invariant, two rules

**Invariant (§15.4.7): the turn's authored form is the single regeneration authority,
emitted exactly once.** Two coupled rules:

1. **Origin-uniform recording (D1).** All introspection records created by one turn
   carry the SAME authored sexp — the turn's original outer form. Change:
   `register_macro_in_module`'s introspection/`macro_sexp` recording, when the defmacro
   arrived via expansion (the processing path knows: `try_expand_sexp` rewrote the top
   form), stores the ORIGINAL form as the regen-facing `sexp` (the expanded defmacro
   stays on `.expanded` and wherever clause recompilation needs it — `macro_sexp`'s
   clause-recompile role is unchanged; only regen's source-of-text changes).
   `generate_fns_and_macros` then **dedupes by authored-form identity** (same span +
   text): N records sharing one authored form emit it once, at the position of the
   earliest `seq`. This also cures the latent sibling cell: a user-typed
   `(begin (defn a …) (defn b …))` today records the begin form under both `a` and `b`
   (same `process_form.rs:629` keying) and would double-emit — same dedup, no extra
   mechanism.
2. **Source-text-first emission (D2).** `generate_fns_and_macros` emits the verbatim
   `Introspection.source` text when present and CONSISTENT, falling back to today's
   reconciled sexp render otherwise. Consistency = the entry's live docstring matches
   the one in the recorded source (the reconciling renderer exists precisely because
   docstrings can be edited out-of-band — agent Document-mode edits, `pull.rs:589/630`;
   those either update the record's source in the same commit or fall back to the
   render for that entry). Rehydration captures the verbatim text segment (it has the
   file text in hand — slice by span) instead of `pretty_print(sexp)`. The reader-
   shorthand loss disappears because the authored bytes are what get written back.

Both guards flip: `persist_macro_defining_macro_use_survives_restart` (D1) and
`persist_defining_turn_preserves_hand_authored_macro_source_text` (D2); the green
boundary control (expression-only session leaves the file untouched) pins that the
regen trigger surface is unchanged.

**D2's unreduced second arm** (hybrid batch/REPL cache-slot break — exemplar-only, six
reductions failed) is NOT designed against here: no mechanism, no fix. Disposition: the
cache-slot sharing is real (entry module `user` and a batch `user.cl` share one manifest
key by construction) but harmless in every reduced shape; re-probe after this cluster
lands, escalate only with a repro (ledger note stands).

### 4.3 Change-set plan

1. **CS-D1**: origin-uniform recording (`process_form.rs`/`form_dispatch.rs`) + regen
   dedup (`save.rs`); unit scenarios per Matrix B rows {defmacro-artifact,
   macro-defining-macro, literal-begin multi-defn} × round-trip/single-authority; the
   D1 guard flips.
2. **CS-D2**: source-text-first emission + consistency check + rehydration
   verbatim-capture (`save.rs`); unit scenarios per Matrix B provenance axis
   {file-originated hand-authored, cache-restored+rehydrated, REPL-authored} ×
   authorship-fidelity; the D2 guard flips.
3. Both ride FIXME 0496's `save.rs` drain (regeneration-grammar test module — the
   proposed-resolution item 2 of that FIXME derives from Matrix B).

Sequencing note: CS-D1/CS-D2 are prerequisites for the S103 T1 full cure (§2) and make
0489's degraded-load reporting cleaner, but neither blocks §1's print.

## §5. Persistence-integrity cluster — 0489 (restart floor)

### 5.1 Root cause (source-verified)

REPL startup drives `register_module` + `wait_inmem_complete` (`main.rs:259/294`)
BEFORE the prompt loop; an entry module landing in `ModulePool::Failed` surfaces as
`Err` → `run()?` → `main.rs:146 process::exit(1)`. The recovery machinery already
exists on other paths: `scheduler.reset_module`/`reset_all_failed_modules`
(`scheduler.rs:1804–1847`, today wired only to `register_dep_for_eval`'s dep-failure
path, `eval.rs:67–73`) and the watcher's non-exiting `error_modules` pattern
(`lifecycle.rs:907–923` — print `[errors: …]`, keep the session, recover on a later
green reload). The startup path simply has no equivalent.

### 5.2 The cure — degraded form-by-form entry load

On entry-restore failure in REPL mode (`Action::Repl` only; `--run`/`--link` keep the
exit-1 contract):

1. **Catch, don't propagate**: the startup error no longer reaches `main.rs:146`.
   Reset the entry's failed scheduler state (`reset_module`), `ensure_module_exists`.
2. **Degraded load**: re-drive the backing source **form-by-form through the ordinary
   eval path** (each toplevel form its own cluster, output suppressed) — batch-cluster
   atomicity is what turns one broken defn into a wholesale lockout; the REPL's own
   per-form semantics are the natural degraded mode. Green forms commit (`f` loads);
   failing forms are collected as `(symbol, error)` pairs — the symbol is the defining
   form's name, which is how the load error **names the broken symbol** (§18.8's
   naming MUST, unachievable from the raw cluster error, falls out of the form grain).
3. **Report** per §5.1: one error line per failed form, naming the symbol and carrying
   the underlying type error; then banner + prompt. The degraded loader is
   **disk-read-only** (it never triggers `regenerate_backing_file` itself), and the
   failed-form registry retains each failed form's **verbatim source text** — because
   subsequent ordinary regen runs rebuild the file from the live table, which the
   failed forms never entered, a regen that ignored them would silently DROP the
   broken definition from the user's file (exactly the §18.8 silent-drop MUST NOT).
   Rule: `generate_module_source` re-emits the retained failed-form text (in `seq`
   position where known, else appended) until the form's symbol is repaired or the
   user removes it externally. This is the §4.2 authorship invariant applied to
   forms that never compiled: authored text is the authority, compile success is not
   a persistence gate.
4. **Error-blocked state** (§14.4 as amended by §18.8): the entry joins
   `error_modules`; while the failed-form set is non-empty, **expression turns are
   refused** with the §14.4 message but **definition turns are always accepted** (they
   are the repair — §18.8's explicit carve-out). A successful definition turn removes
   its symbol from the failed set; when the set empties, the entry leaves
   `error_modules` and the next regen writes a green backing file. (Today
   `error_modules` gates nothing — its doc-comment claims eval blocking that was never
   wired; this change-set wires it, for the watcher path too, closing that latent
   §14.4 gap in the same stroke.)

The 0489 guard flips (prompt reached, repair accepted, `(k "abcd")` → 4 — the
form-by-form degrade is what makes `f` available to the repair turn). Broken-ness
round-trip semantics (§8 of session-transaction.md) are unchanged: broken-ness is
still reconstructed as load-time compile errors, never as persisted traps.

### 5.3 Change-set plan

**CS-0489** (one change-set, `main.rs` + `lifecycle.rs` + eval gate): startup catch +
degraded form-by-form loader (reuses the eval form chain — no new orchestration
protocol) + failed-form registry + §14.4 expression gate with definition carve-out.
Unit scenarios: Matrix A row "backing BROKEN" cells (reaches-prompt, repair-def
accepted, expression refused pre-repair, error clears on green, `--no-cache` same) +
the lifecycle decision-path tests FIXME 0496 item 3 asks for (extract the
degraded-load decision as a pure seam — which forms failed, what clears — so
`lifecycle.rs` gains its first unit module). E2E: the guard + an L-S2 sibling for the
expression-refusal leg (not yet pinned anywhere).

## §6. File-backed dev-loop — D3 + FIXME 0487

### 6.1 Root cause (source-verified) — the module-env install gap

The session-side module environment lives in three companion structures populated
ONLY on the fresh-typecheck path: `prelude_fallback`
(`inject_prelude_if_needed`, `dependency.rs:1318`), `module_aliases`
(`install_imports` / `register_submodule_alias`), and
`typecheck_products` (`source_text` at `dependency.rs:483`). **The cache-restore
installs populate none of them** (`install_cached_table`, `cache_restore.rs:247–260`;
`introduce_module` CachedLoad branch, `lifecycle.rs:537–546`). A cache-restored module
therefore typechecks its next turn with no prelude fallback bit (→ `undefined
variable: =`, `unknown type Int (from module '')` — D3's reduced face and 0487 items
1–2), no aliases, and no rehydration source.

**Sharper finding**: `TypecheckProduct.file_path` is **never `Some` on any path** —
the only constructor site is `worker.rs:794–799` with `file_path: None`, and no
assignment site exists. So the §4.2 rehydration chokepoint
(`redefine.rs::resolve_recheck_sexps`) and the T2 `module_grain_reload` are dead as
wired for every module — this is D3's "definition source unavailable" face waiting
behind the env wall, and it also explains why those faces only appear at scale.

### 6.2 The cure — module-env established at every install route

**Invariant (Principle 18/20): a module's session-env companions (fallback bit,
aliases, source-file authority) are established at INSTALL time, uniformly across
every route a module enters the session** — fresh typecheck, cache restore, blank
`/mod` creation — not as a side effect of one route's Pass 0.

1. **`file_path` becomes a real authority.** Set `typecheck_products.file_path =
   Some(source_path)` at every site that knows the module's source file: the fresh
   dep-load path (`dependency.rs:483` sets `source_text` already), the cache-restore
   installs (the restore is keyed by the source file it hashed), and entry
   registration. Consumers converge: `resolve_recheck_sexps` rehydration,
   `module_grain_reload`, and `regenerate_backing_file` (whose private
   `{root}/{module}.cl` fallback stops being load-bearing).
2. **Companion recompute at restore.** The two cache-install sites call one shared
   `install_module_session_env(table, …)` helper that (a) derives the prelude-fallback
   bit from the restored table's own structural fields (`imports` — same predicate as
   `inject_prelude_if_needed`, extracted and shared, Principle 7); (b) re-registers
   import-`as` aliases and submodule short-name aliases from the restored `imports` /
   `submodules` fields. `/dev` confirms the extracted predicate agrees with
   `sexps_reference_prelude` on the structural-field representation (unit cell:
   module-importing-prelude-explicitly stays OFF).
3. **Blank `/mod M` creation** (`handle_mod` → `set_current_module` →
   `ensure_module_exists`) runs the same helper (bit ON for a blank module — it cannot
   be referencing prelude). `/dev` additionally confirms why the per-cluster
   `inject_prelude_if_needed` does not already repair restored modules on their first
   eval turn (the D3 guard proves it doesn't; pin the gating in a unit test rather
   than a comment).
4. **Re-probe D3's unreduced faces** after 1–3: the cross-module "definition source
   unavailable" and revert-no-heal exemplar faces should be reachable (or gone) once
   rehydration can fire; extend the guard file per what falls out, per the partial-
   reduction note in `tests/repl_persist_redefine.rs`.

Guard flips: `redefine_file_backed_module_symbol_after_cache_restore_works_like_fresh`;
the fresh-session control stays green (it pins the invariant the restored session must
match).

### 6.3 FIXME 0487 item 3 — FQ introspection arguments + project-wide `/refs`

- **FQ name arguments**: one shared resolver `resolve_symbol_arg(name) ->
  (ModuleFullPath, bare)` — `rsplit_once('/')` + `substitute_module_alias`, the shape
  `broken_status_line` already uses — adopted by `describe_symbol` (drives
  `/info`/`/sig`/`/doc`), `get_introspection` consumers (`/source`, `/sexp`, `/clif`),
  and `/refs`. The cascade report prints FQ names; every introspection command MUST
  accept what the report prints (0487's operational complaint).
- **`/refs` feed**: `scan_referers` already scans all module tables but reads
  introspection records (`body_references`) — absent for cache-restored modules, so
  cross-project refs silently vanish. Add the `redefine::ReverseIndex` as the primary
  feed for callable referents (`callers_of(fq)` over the serialized, 0470-widened
  `callees` — present for cache-restored modules by construction), textual scan
  retained for non-callable referents (type names in annotations); union + dedup.
  This is also the §18.3 "preview the affected set" companion 0487 asks for — same
  index, same grain as the transaction itself (Principle 7).
- `/sig` on an imported name printing only the import line (minor 0487 tail): resolve
  through the import chain before rendering, as `/doc` already does — fold into the
  same change-set.

### 6.4 Change-set plan

1. **CS-D3a**: `file_path` authority (item 6.2.1) + companion recompute at restore
   (6.2.2) + blank-`/mod` env (6.2.3). Unit scenarios: Matrix D full grid — provenance
   × env-dimension, incl. negatives (explicit-prelude-importing module keeps bit OFF
   after restore; aliases don't leak across modules). D3 guard flips.
2. **CS-D3b**: D3 face re-probe + guard extension (6.2.4) — may be empty if the faces
   dissolve.
3. **CS-0487**: FQ resolver + `/refs` ReverseIndex feed + `/sig` import-chain (6.3).
   Unit: repl handler tests through the facade (FIXME 0496's `repl.rs` drain rows).
   E2E: L-S3 lane rows (introspection-accepts-what-reports-print).

## §7. Display/diagnostic batch (capacity-gated tail)

Brief sketches, ordered smallest-first. Items 7.1–7.3 are trivially small (one seam,
one change-set each, guards already RED); 7.4–7.5 need one confirmation step first.

### 7.1 FIXME 0491 — `__expr` joins the transaction (trivially small)

Root cause: the eval wrapper's `Def` carries real `callees`, so `ReverseIndex::build`
records it as a caller and the closure/report pick it up (both directions — break and
revert). Cure at the feed, not the rendering: `ReverseIndex::build` skips callers whose
symbol is `is_gate_exempt_internal` (`__expr`/`__macro_*`) — they never join closures,
never get re-typechecked/marked, never appear in any report section (incl. §1's
`stale:`). Safe by the frozen-world argument: a stale wrapper is never re-invoked (each
expression turn redefines it before invoking). Unit: reverse-index exclusion cell +
report-negative (Matrix C `__expr` column); both 0491 guards flip.

### 7.2 Trap-message §18.5 format (trivially small)

Root cause (five layers, traced): the trap body (`compose_provenance`) is wrapped by
intrinsics' `runtime panic: ` prefix (`panic.rs:88`), then `program_outcome_to_result`
(`pipeline.rs:165–177`) wraps it in `CranelispError::CodegenError` with a second
`runtime error: ` prefix and a synthetic span, whose Display adds
`codegen error at 0..0:`, and the REPL adds `Error: `. Cure — **int-side only, no
`cranelisp-types` change**: `program_outcome_to_result` (the single chokepoint reading
the runtime-error slot) returns a dedicated int-side runtime outcome instead of a
`CodegenError`; the REPL/`--run` printers render it per §18.5 exactly —
`runtime error: {payload}` with the known `runtime panic: ` slot prefix normalized
away at that chokepoint, no span, no `Error:`/`codegen error` wrappers. (If /dev
finds a `CranelispError::RuntimeError` variant cleaner, that is a `cranelisp-types`
edit → FIXME `target: /arch` first; the int-side shape avoids the cross-crate cascade
and is the recommended cut.) Applies to ALL runtime panics, not just traps — the
guard (`trap_presented_in_normative_runtime_error_format`) flips; existing tests
asserting the old wrapper text re-anchor in the same change-set.

### 7.3 FIXME 0486 — bare lookup corrupts `/info`/`/source` (trivially small)

Root cause (traced): `eval()`'s source-capture writer (`eval.rs:130–146`) fires for
ANY `EvalResult::Def` and overwrites `introspection[fq].source` with the turn's
verbatim text — and a bare defined-symbol lookup returns a display-only
`EvalResult::Def` from `check_bare_symbol_introspection` (`eval.rs:578–583`), so the
turn text `"solo"` clobbers the authored source. (`.sexp` survives; both display
paths prefer `.source`.) Cure: mark the display-only result — `EvalResult::Def` gains
`defined: bool` (or a distinct `Describe` result) — and the writer fires only for
genuine definition turns. The writer is otherwise CORRECT and load-bearing: for real
definition turns it records the authored text that §4.2's source-first regeneration
emits — coordinate the two change-sets (same invariant, Matrix E). Unit: Matrix E
cells (bare lookup MUST NOT touch the record; defn/redefinition turns update it;
healthy + broken arms). Guards: both 0486 guards + control.

### 7.4 FIXME 0490 — phantom-member misleading error (small, one confirmation)

Desired behavior (the FIXME's proposed resolution, adopted): when the qualifier of
`mod/sym` (alias-substituted) names a module that is **loaded** (or loadable), a
missing member reports member-not-found against THAT module — `module 'primitives'
has no member 'vec'` — with the member the user typed, the real span, and a
did-you-mean hint when the bare name resolves in scope; module-not-found fires only
when the qualifier resolves to no module. As-built, a member miss on a loaded module
falls through to a submodule-candidate probe that synthesizes `<current>.<qualifier>`
(`user.primitives`) and then fails module-not-found with a `'…/...'` placeholder and
`span 0..0` (`dependency.rs:352` + the `resolve_current_module_relative` family) —
three lies in one line. Change-set: member-not-found short-circuit at the gap/dep
derivation seam (before `drive_module_dep`), + thread the referencing symbol and
span into the not-found message (drop the `'…'` placeholder). One confirmation step
first: whether the `<current>.<qualifier>` synthesis happens int-side or in
typecheck's resolution — if typecheck-side, the message fix stays int-side but the
ordering fix files FIXME `target: /typecheck` with this section + the repro as brief.

### 7.5 FIXME 0484 — import-shadow order dependence (conditional on /spec)

/spec is ruling precedence concurrently; the guard is authored against shadow-wins
(§8.6.1 layer 2) and re-anchors if ruled otherwise. Mechanism status (traced this
phase): the commit side is CLEAN — a defn over a prior `Import` classifies `New`,
takes a fresh slot, and replaces the table binding (`redefine.rs:143–144`,
`worker.rs:613`); bare-name type resolution re-derives per cluster from the live
table; the REPL carry-forward state is not the typecheck `CheckState`. The pin
therefore lives in **durable name-adjacent artifacts of the first call** — best
evidence: the per-cluster overload/dispatch rehydration
(`cranelisp-typecheck/src/form.rs:211–235`, `state.resolved_overloads.entry(name)
.or_insert(…)` — first-write-wins keyed by BARE name) plus surviving
variant/mono entries the defn commit does not clear. Plan, in order:
(1) `/dev` confirms the pinning artifact against the guard fixture (one trace
session; the stdlib-free repro exists); (2) if the artifact is typecheck-side (the
rehydration guard), the fix is `/typecheck`'s — file FIXME `target: /typecheck`
naming the artifact + the guard (minimal-repro rule satisfied); if int-side (stale
variant entries surviving the commit), the fix is the defn commit clearing
name-derived artifacts whose terminal source is the displaced import; (3) either
way, `/info`-agreement needs no separate fix — introspection already describes the
shadow; call resolution joins it. Do not fix before /spec's pin lands.

## §8. Wave ordering + dependency notes (input to /sprint Phase 4)

All /int waves are **capture-neutral** per the Phase-2 Q1 classifier (no emission
change for green programs) — they may run before, parallel to, or after Block B's
golden-CLIF capture, and serially with respect to each other (single source-touching
agent).

| Wave | Content | Depends on |
|---|---|---|
| **A-1** | §1 T1 print + §7.1 0491 + §7.3 0486 (same `redefine.rs`/`eval.rs` seams; 0491's exclusion helper is §1's stale-set filter) | nothing — /repl §18.1.1 already landed |
| **A-2** | §4 CS-D1 → CS-D2, then §5 CS-0489 (lifecycle/save seams; 0496 unit drain rides) | nothing external; internally D1 before D2 (both touch `save.rs` emission) |
| **A-3** | §6 CS-D3a → CS-D3b → CS-0487 | nothing external; D3b after D3a by construction |
| **A-4** (capacity tail) | §7.2 trap format; §7.4 0490; §7.5 0484 | 0484: **/spec precedence pin** + mechanism confirmation (possible `/typecheck` handoff); 0490: one synthesis-site confirmation (possible narrow `/typecheck` FIXME); trap format: none |

- **Waits on /spec**: only 0484 (§7.5).
- **Waits on /repl**: nothing in-sprint (§18.1.1 and §18.5 wording are landed; the
  module-grain reload report wording is an S103 dependency of the T1 full cure only).
- **Waits on /arch types change-set (Block B)**: nothing — no item here touches
  `cranelisp-types` (the §7.2 cure is deliberately cut int-side to keep it that way).
- **QA-first interlock**: L-U1 (the §18.1.1 print e2e) precedes A-1's close; L-S2/L-S3
  lane rows ideally exist before A-2/A-3 close (the 12 existing guards already cover
  the defect cells; the lanes add the grid neighbours).
- **T1 full cure**: OUT — S103 (verdict §2). A-2 + A-3 are its preconditions and land
  this sprint regardless.

## §9. Quality attributes (per /design stewardship)

| Attribute | Disposition this wave |
|---|---|
| Simplicity | Every cure is a uniformity fix at an existing chokepoint (one recording convention, one install helper, one outcome channel, one error chokepoint) — no new protocols, no new state machines (Principle 6). |
| Maintainability | The three "two sites disagree" defects (D1 recording, D3 install routes, trap wrapping) each collapse to a single authority (Principle 7); the install-time env invariant is structural (Principle 18/20). |
| Observability | §1 makes the T1 downgrade visible (the sprint's headline honesty item); §5 makes startup failure name symbols; §7.2 makes runtime errors render their category truthfully. |
| Concurrency-safety | Untouched — no new shared state; all new work is eval-thread-synchronous or startup-sequential. The §5 degraded loader reuses the eval form chain, inheriting Invariant SW. |
| Performance | §1's `ReverseIndex` scan runs only on T1 downgrade turns (L-D1 pin intact); §5's form-by-form load runs only on the already-failed startup path; §6 adds O(imports) work per module install. No perf gates touched. |
| Testability | §3's five matrices are the explicit scenario space; FIXME 0496's drain is their unit half; `lifecycle.rs` gains its first unit module via §5's pure-seam extraction (Principle 23). |

## Next skills

- `/qa` — L-U1 first (carries the §18.1.1 print e2e), then L-S2/L-S3 from Matrices
  A/D; the 12 existing guards are the flip set, itemized per section above.
- `/dev` (src/) — Wave A-1 first (small, independent); then A-2, A-3, A-4 per §8;
  FIXME 0496 unit briefs derive from §3's matrices; two conditional narrow FIXMEs to
  `/typecheck` may fall out of §7.4/§7.5 mechanism confirmation.
- `/spec` — 0484 precedence pin (§7.5 is conditional on it).
- `/repl` — nothing owed in-sprint; S103 module-grain report wording rides the T1
  full cure.
- `/sprint` — §2's verdict (T1 full cure → S103) and §8's table are the Phase-4
  inputs.
