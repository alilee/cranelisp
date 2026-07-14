# Sprint 109: Agent observability + REPL/search/resolution batch + dotted-Ctor capability

**Status**: PHASE 5 LANGUAGE (ACTIVE)

**Goal**: Land the agent-context **observability** substrate as the lead, plus the
REPL/search/resolution/persistence defect batch surfaced through S108 testing, the
full dotted-`Type.Ctor` constructor capability (same-named constructors across
types), and the four accepted S108 typecheck-audit hygiene items.

**Audit**: `src/` (rotation — arch P2 ruling: prefer `src/`; the observability lead
lands in `src/agent/`, heaviest-touched context this sprint, and frontend does ~nil
dotted-ctor work so the draft's frontend citation was weak. `cranelisp-typecheck`
was S108 — no back-to-back). Confirm at Phase 4.

## Scope

Continues the S108 "testing-driven defect-fix" flavour, anchored on the
observability increment the user prioritised. **Broad** batch (user-chosen S109
Phase 1). Six buckets:

### 1. Agent-context observability — LEAD (0577 thread A)
Enrich the §27 JSONL activity log (`repl/spec.md §17.20.3`, `src/agent/log.rs`) with
six explanatory fields, each **derived from harness-visible events** (no new model
narration): `question` on a `pull` (+ require the arg on probe tools), `error_class`
on a `pull` result, `give_up` cause + dominant error class, a context-version stamp
(`primer_hash`+`harvest_len`), a `scenario` tag, step accounting. Built **against**
the metric definitions in `tests/plan/agent-context-tuning.md §4` (the acceptance
spec — each field earns its place by feeding a named metric). Thread **B** (probe
output → private channel, not the user session) included. Threads **C** (primer →
99% content) and **D** (gap loop) **deferred with scenario testing** (user
sequencing — you tune the primer from mined signal, not blind).

### 2. Dotted-`Type.Ctor` full capability (RED guard in scope; cancels audit R-3)
Permit same-named constructors across in-scope types — **define AND import** two
types sharing a constructor name (`Maybe.Some`/`Option.Some`, `Network.Address`/
`Customer.Address`), referenced/disambiguated by the dotted form, exactly as
same-named **fields** already coexist (§8.5.2 modules.md:743, tested). User-confirmed
capability (S109 Phase 1). Fixes the input/output asymmetry (the REPL prints
`Color.Red` but rejects it as input) and the ctor/accessor inconsistency (`Box.v`
resolves; `Color.Red` doesn't).

**Mechanism (ARCH-RULED Phase 2 — NOT resolver-only): mirror the field
inverted-model.** Registration mints the canonical `Type.Ctor` key as the real
got-slotted constructor `Def` in the home module; the bare ctor name becomes an
**alias** entry poisoned to the existing `ModuleEntry::Ambiguous` sentinel on
distinct-terminal collision — reusing the `adt.rs` field-accessor machinery
(§8.6.5 "duplicate names contest the bare ALIAS, not the canonical accessors"), NOT
inventing a second resolver branch. The dotted resolver then probes the canonical
key for ctors exactly as it does for fields — **one member-resolution codepath**.
**Size resolved: MEDIUM, one registration-led change** — the single-type case
(`Color.Red`) falls out for free once the canonical key exists. **`/testing`'s
resolve-only `enumeration-miss` is the correct test-CLASS label but the WRONG fix
scope; staging resolve-only first is a forbidden Principle-8 interim** (its bare-key
probe would be deleted same-sprint).

**Scope Phase 3 MUST cover** (arch amendments):
- **Pattern position is in-capability** — bare `(Some x)` poisons; dotted
  `(Maybe.Some x)` disambiguates (else values are constructible but unmatchable).
  Pattern-*resolution* work in typecheck (frontend lands `Pattern::Constructor.name`
  unsplit; ~nil reader work). `/spec` framing + `/testing` twin cover BOTH value and
  pattern position.
- **Product dual-facet corner** — a product ctor (type-name == ctor-name,
  `type_def: Some(..)`) keeps its single key at the type name; canonical dotted form
  is degenerate. `/design` (typecheck) settles explicitly.
- **§8.6.5 not §8.6.4** — same-named ctors are alias-poison territory (like fields),
  NOT def-over-binding rejection; that is the semantic content of "registration
  permits coexistence." `/spec` frames accordingly.
- **`/spec` clarification** (framed for user sign-off): constructors coexist +
  disambiguate by `Type.Ctor` in value AND pattern position, §8.5.2.
- **`cranelisp-types` touches** (Phase-3 `/arch` change-set, consolidated with 0573
  + 0567): `member_key(type_name, member)` helper (additive pub, kills the
  hand-rolled `format!("{}.{member}")` at 3 sites); `type_ctor_names` walk to
  canonical keys (no signature change); reuse existing `Ambiguous`/alias (no new
  DTO — `DefKind::Constructor.type_name` already carries (Type,Ctor) identity).
  **`CACHE_SCHEMA_VERSION` bump** (backend, currently 16) same change-set — keying
  is a `.meta.json` content-meaning change. `public-api.txt` regen + `interfaces.md`.
  No ABI/GOT impact.

RED guard: `tests/spec_08_modules.rs::dotted_constructor_in_value_position_resolves`
(`class=enumeration-miss`); `/testing` adds the two-same-named-ctors twin (value +
pattern; couples with 0581's same-named-ADT fixture family — note the axes differ:
0581 = same *type* name across modules, bucket 2 = same *ctor* name across types).

### 3. REPL/search/resolution/persistence defect batch
- **0567** — resolve prelude-retry filters terminal not head (`/dev` typecheck).
- **0568** — ambiguity error leaks internal `__expr` binder (`/dev`).
- **0569** — `/search` macro rows show bogus `:primitives/Int` (`/dev` + `/repl` §17.19.2 pin).
- **0571** — FQ-symbol ref → opaque codegen leak. **RULED A + arch mechanism review DONE (P3):** the park/enqueue/resume edifice **already EXISTS and works** (S78 gap protocol + FIXME-0268 autoload; arch drove `collections.vec/count [1 2 3]` → `:Int 3` live). So ruling A is largely implemented; §8.5.4 SHOULD→MUST just codifies it. **The real defect is 3 things, NOT a missing load:**
  1. **Value-position ref to a slot-less generic template → backend leak** (THE committed defect). `count` is generic ⇒ `UserFnState::Polymorphic` ⇒ slot-less; value-position refs never mint a mono (minting is call-site-keyed) ⇒ reaches `backend/literals.rs:192`. Fix: typecheck **mints a mono at the inferred concrete type OR dies check-side** with a §3.11-style annotation-required error; REPL FQ display takes the **same introspection path bare names use** (mode+name-uniform). `import` does NOT cure it (proves it's not a load gap); mode-uniform (no divergence). This is `/testing`'s failing repro (D1).
  2. **FQ-cycle MISATTRIBUTION (RED) + pool diamond RACE (latent nondeterminism, ≥2 workers)** — a predicate mismatch: typecheck's gap fires on module-map ABSENCE only, but int's "loaded" = presence AND terminal. Cure: `resolve_qualified` member-absent arm yields the gap **unconditionally**; INT decides (absent→load+park; present-non-terminal→park; terminal→honest "module X has no member Y"). Keeps typecheck scheduler-free; fixes cycle-misattribution AND the diamond race **for free**.
  3. **Error quality** — doubly-wrapped msg, "codegen failed for /", synthetic `0..0` spans (should be the reference site).
  **Wave:** same `checker.rs::lookup`/`resolve_qualified` vicinity as bucket 2 — B2 wave scope now INCLUDES the member-absent-gap reshape + int gap-arm decision logic. **Public-API:** no new type (ResolutionGap/CheckError::Gap suffice); ONE additive `#[non_exhaustive]` `ResolutionGap` variant pre-approved as contingency only. **P8:** forbidden fix-shims — backend message patch, REPL-only display special case, int "undefined variable" pattern-match (leaves the race alive). §8.5.4 **10-edge list** → `/spec` (relayed); **A/B/C/D test rows** → `/qa` plan (C = the in-flight race, the rigorous core; D1 = the failing repro).
- **0573** — product-form `deftype` NOT persisted to backing `.cl` file (`/dev` `src/`; DEFECT — silent data loss, repro owed).
- **0572** — unify `/search`/sig/`/info` displays + drop `<closure>` value token (`/repl` design).

### 4. Settled-semantics documentation + error quality
- **0575** — `fn` is single-arity (settled): `/spec` doc + `/dev` parse-error quality.
- **0576** — multi-arity `defn` arities type-checked independently (settled): `/spec` doc + `/dev` ambiguous-type diagnostic (names which param/clause; couples with 0568).

### 5. Module visibility — 0570 (RULED P3: NOT a new mechanism; enforce existing `mod-`)
`/search` surfaces symbols from public test submodules with valid-but-unwanted import hints. **Ruling (user, P3):** module privacy ALREADY exists — §8.2.3 `(mod- name)`: "Other modules MUST NOT import from or reference names in a private submodule" (already `[Tested+Neg …mod_dash_private_submodule_not_importable_from_peer_neg]`). The defect is that stdlib test submodules are declared **bare `(mod test)` = public** (`stdlib/CLAUDE.md:94` mandates bare `mod`). NOT a `/spec` normative decision. Fix:
- **`/stdlib`** — remark test submodules `(mod- test)` (private). First VERIFY `mod-` works with the child-file test pattern (`<module>/test.cl`) — the bare-`mod` convention was deliberate; confirm no extraction/codegen reason blocks `mod-`.
- **`/dev`** — ensure the `/search` index + import filter **honor `mod-`**: §8.2.3's tested-neg covers peer-import rejection, but search-index *surfacing* of private-submodule symbols is a separate conformance gap (untestable today because the modules are public). `/testing` twin: a `mod-` submodule's symbols MUST NOT appear in `/search` and MUST NOT be importable from a peer.
- **`/spec`** — at most a one-line §8.2.3/§17.19.2 clarification that search-surfacing counts as "referencing." No new visibility subsection.

### 6. S108 typecheck-audit hygiene (accepted R-1/R-2/R-4/R-5 → FIXMEs 0578–0581)
- **R-1** (FIXME 0578, `/design` typecheck) — rewrite `traits.md` against as-built model + triage doc sprawl. Medium.
- **R-2** (FIXME 0579, `/dev` typecheck) — doc/naming sweep (stale "outer scope"/S78 rustdoc, `resolve_entry_in_current_module` rename). Small.
- **R-4** (FIXME 0580, `/dev` typecheck + `/design` sign-off) — split the 3,962-line `program.rs`. Medium.
- **R-5** (FIXME 0581, `/dev` typecheck) — S87 residue batch (half-FQ diagnostics, `_=>None` silent drop, `"user"`-defaulting helper). Small; wants a `/testing` twin repro.

### Out of scope (deferred, with rationale)
- **0577 threads C/D** (primer content + gap loop) → deferred WITH scenario testing; tune the primer from the mined observability signal, not blind (user sequencing). Target: sprint after observability lands + scenarios seeded.
- **0553** (ownership instantiation entry point, `/dev` typecheck) — outside this sprint's theme; carry.
- **0463** (examples network-poll shape) → Phase 6 `/examples` if reached, else carry.
- **0050** (list/seq pretty-printer) — remains deferred (blocked on display-protocol design that does not exist). **0052** (docs learn-system) — user-deferred at S107 close. Neither is 2×-forced.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0567 | /arch | **RESOLVED** | P3 commit `9c69b203` — head-visibility fix + 2 pins; FIXME deleted |
| 0568 | /dev | open | `__expr` internal binder leaks into ambiguity error |
| 0569 | /dev (+/repl pin) | open | `/search` macro rows show bogus `:Int` |
| 0570 | /stdlib + /dev | open | RULED P3: enforce existing `mod-` — /stdlib marks test mods private, /dev makes search/import honor it; /spec ≤1-line clarify |
| 0571 | /dev (+/spec Q) | open | FQ-unimported → opaque codegen leak; DEFECT, repro owed |
| 0572 | /repl | open | unify search/sig/info displays; drop `<closure>` |
| 0573 | /dev (src/) | open | product-`deftype` not persisted; DEFECT (data loss), repro owed |
| 0575 | /spec (+/dev err) | open | `fn` single-arity — doc + parse-error quality (settled) |
| 0576 | /spec (+/dev err) | open | multi-arity `defn` independent — doc + diagnostic (settled) |
| 0577 | /repl (+/dev) | open | agent-context observability (thread A in scope; C/D deferred) |
| 0578 | /design (typecheck) | **RESOLVED** | P3: traits.md rewritten to as-built model + doc-sprawl triage; FIXME deleted |
| 0579 | /dev (typecheck) | open | R-2 doc/naming sweep (filed S109 P1 from S108 audit) |
| 0580 | /dev (typecheck) | open (signed-off) | R-4 program.rs split — P3 cut signed off (`program-decomposition.md`); /dev tail (move+verify) lands LAST Phase 5 |
| 0581 | /dev (typecheck) | open | R-5 S87 residue batch (filed S109 P1 from S108 audit) |
| 0582 | /design (typecheck) | open | correct `dotted-ctor-registration.md §6` blast-radius table (filed P5 by /arch) |
| — (RED) | /dev (typecheck) | test | dotted-ctor full capability — committed guard IS the record (no FIXME) |
| 0553 | /dev (typecheck) | carry | ownership instantiation entry point — out of theme |
| 0463 | /examples | carry | network-poll example — Phase 6 candidate |

## Audit disposition (S108 → `audits/cranelisp-typecheck-s108.md`)

Disposed with user, S109 Phase 1:
- **R-1 accepted** → FIXME 0578 (/design typecheck).
- **R-2 accepted** → FIXME 0579 (/dev typecheck).
- **R-3 DECLINED** — the dotted-`Type.Ctor` drop. User chose the **full-capability
  fix** instead (scope bucket 2): same-named constructors across types are a
  first-class pattern (option/result-likes, `Address`/`Node`), the dotted form is
  their namespacing mechanism, and the language already *displays* the dotted form
  it currently rejects as input. Rationale appended to the assessment.
- **R-4 accepted** → FIXME 0580 (/dev typecheck + /design sign-off).
- **R-5 accepted** → FIXME 0581 (/dev typecheck).

## Normative rulings (Phase 3 — RESOLVED with user 2026-07-13)
1. **Same-named constructors across types — CONFIRMED.** Coexist as **§8.6.5
   alias-poison** (bare name contests; `Type.Ctor` always resolves, VALUE + PATTERN
   position), NOT §8.6.4 rejection. Mirrors same-named fields. Lands §8.5.2 + §8.6.5
   + §6 (`/spec` drafted; user signed off). `/spec` to land text.
2. **Module visibility (0570) — RULED: enforce existing `mod-`** (NOT a new
   mechanism; §8.2.3 already specifies private submodules + the MUST-NOT-import,
   tested-neg). Stdlib test mods are bare `(mod test)` = public. → `/stdlib` marks
   them `(mod- test)`; `/dev` makes search/import honor `mod-`; `/spec` ≤1-line
   clarify. See bucket 5.
3. **FQ-ref-without-import (0571) — RULED A: FQ ref RESOLVES** (§8.5.4 SHOULD→MUST,
   file-backed matches seeded `primitives`). **Mechanism (user): typecheck PARKS the
   current module, ENQUEUES the dependency, RESUMES on completion** (v4 scheduler
   edifice) — **needs a dedicated `/arch` mechanism review + rigorous
   parking/resumption testing** before Phase 5. Diagnostic fix unconditional. See
   bucket 3. `/spec` HOLDS the §8.5.4 text pending the arch mechanism review (in
   case park/resume surfaces spec-relevant edges: load-failure, cyclic dep).
4. **Settled-doc 0575/0576 — CONFIRMED wording** (`fn` single-arity §4.5; multi-arity
   `defn` independent §5.1.2). `/spec` to land.

## Architecture review (Phase 2)

**Verdict: SIGN-OFF, contingent on three revisions (all incorporated above; arch
pre-approved the wording — no re-review round).** Structure coherent, debt-first
weighting right, lead bucket genuinely low-risk.

**Three revisions (incorporated):**
1. **0567 reassigned /dev→/arch** — `target: /arch`; seam is arch-owned
   `cranelisp-types/resolve.rs::resolve_with_prelude` L523–531. `/arch` lands it as
   a small Phase-3 change-set (head-visibility filter + failing unit pin first;
   behaviour-invariant for the stock prelude; no public-API/cache impact).
2. **Bucket 2 mechanism named** — field inverted-model mirror (canonical `Type.Ctor`
   keys + poisoned bare alias), NOT resolver-only; size = MEDIUM one registration-led
   change; pattern-position + product-facet + §8.6.5-not-§8.6.4 added to `/spec`
   framing; cache-schema-bump + types-crate touches recorded. (See bucket 2.)
3. **0572 + thread B ride the E4 styled seam** (`design/arch/repl-styling-seam.md`)
   — 0572's unified display is the shared `:Type <subject> ; metadata` envelope;
   thread B's probe channel is the E4 agent-gutter producer. Do NOT mint a fourth
   format. Pin in the `/repl` Phase-3 dispatch.

**Per-bucket public-API / cross-crate impact:**
- **B1 Observability** — NONE (confirmed `src/agent`-local + `repl/spec.md`;
  `LogEvent`/`classify_error`/probe-tool schemas all int-private; 6 fields map 1:1
  to the `agent-context-tuning.md §4` metrics).
- **B2 Dotted-ctor** — `cranelisp-types` edits (Phase-3 `/arch`): `member_key`
  helper, `type_ctor_names` walk, reuse `Ambiguous` machinery (no new identity type).
  `CACHE_SCHEMA_VERSION` bump (backend). `public-api.txt` regen + `interfaces.md`.
- **B3 Defect batch** — 0573: **`ModuleEntry::type_def_info()` additive pub method**
  (Phase-3 `/arch`; the product `deftype` has no `TypeDef` entry — it's a
  `Def{Constructor{type_def:Some}}` facet, so `save.rs:696 generate_types` skips it;
  promote the single "answers as a type" reader, `save.rs` + typecheck
  `type_def_view_of` delegate; read-side only, NO cache bump). 0567: arch in-crate,
  no shape change. 0568/0569/0571: none anticipated. 0572: none (int-side).
- **B4 Settled-semantics** — NONE (spec prose + in-crate diagnostics).
- **B5 Visibility Q (0570)** — none this sprint. **Arch input to the `/spec` frame:**
  if the user picks a naming-convention rule (`.test` suffix), Principle 19 requires
  it be a **declared module role/attribute set at the load/mount boundary** (the
  `prelude_fallback`-bit precedent), never a name-probe inside resolution — carry
  that constraint so the choice is representable either way.
- **B6 Hygiene** — NONE; 0580 must show a zero-diff `public-api.txt` (`/review`
  checks the pure-decomposition claim).

**0571 direction:** an unresolved name should die in typecheck `lookup`
(`ResolutionGap` carrier — no new cross-crate type); reaching codegen means a path
tolerates a check-time miss. Investigate-before-fix (call-chain evidence first); fix
at the shared typecheck/resolution seam (all modes), not a codegen message rewrite.
Normative Q3 changes only which *success* path exists; the diagnostic seam is the
same either way — say so in the user frame.

**0573 framing for `/qa`:** the repro is the **deftype-shape × persistence matrix**
(sum, product; file-content + reload-retains-type-and-accessor) — the standing
"coverage by definition variants" category made flesh; the fix cures the
TypeDef-vs-product-facet mirror class (3rd instance), not a `save.rs` match-arm patch.

**Consolidation:** the three `cranelisp-types` items (0567 fix, `member_key` +
`type_ctor_names`, `type_def_info`) land as **ONE Phase-3 `/arch` change-set** feeding
the downstream waves.

**Phase-4 wave hints (recorded for Phase 4):**
- typecheck is the serialization hotspot (B2, 0567, 0568, 0576-diag, 0579, 0580,
  0581 all touch it — serial anyway). **Order: B2 registration/resolver → 0581
  residue (shares same-named-identity display surface + fixture family with B2) →
  0579 doc sweep → 0580 program.rs split LAST** (mechanical split rebases trivially
  when nothing follows; `/design` sign-off on the cut can happen early/parallel).
- 0571 same wave as B2 or strictly after (same `checker.rs::lookup` vicinity), not
  interleaved.
- 0568 ↔ 0576 diagnostic pair — one `/dev` deployment.
- Thread B + 0572 + 0569 — one `/repl`-design + `/dev`(int) wave under the E4 seam.

## Skill plans (Phase 3)

{Pending — populated Phase 3.}

## Waves (Phase 4)

**Constraint:** worktree isolation is broken → **source-touching work is SERIAL**
(one editor at a time). "Waves" below are logical groupings with a pinned execution
ORDER; read-only/verify steps may overlap. Typecheck is the serial hotspot (arch P2
order is binding). Design is complete for every wave (Phase 3).

### Stage 1 — QA-first (one `/testing` dispatch, sprint-wide) — FIRST
`/testing` authors the full failing e2e set from `PLAN.md §S109` (all RED rows +
`// defect:` lines; verify-first rows checked). Failing-not-ignored. **Early gate
inside Stage 1:** MV-4 precondition — `/testing` (or `/stdlib`) VERIFIES `mod-` works
with the child-file test pattern (`<module>/test.cl`). If it fails, it blocks
0570/MV-1 + `/stdlib`'s remark → surface immediately (re-scope 0570 or file a defect).

### Stage 2 — per-crate D/D/R, PINNED ORDER

**W1 — Typecheck critical chain (SERIAL, arch-pinned; the longest pole):**
1. **Bucket 2 dotted-ctor + 0571 gap-reshape TOGETHER** (same `checker.rs::lookup`/
   `resolve_qualified` vicinity). Bucket 2: canonical `Type.Ctor` keys + bare-alias
   poison (adt.rs), shared dotted resolver (value+pattern), product facet,
   `type_ctor_names` walk + **CACHE_SCHEMA_VERSION 16→17**, blast-radius BR-1
   (exhaustiveness `.`-strip) + BR-2 (IO `internal`-ctor exclusion), `member_key`
   sweep (incl. `infer.rs:235`). 0571: member-absent → **unconditional gap** + int
   gap-arm decision (load/park/honest-diagnostic) + value-position mint-or-reject
   (D1) + span + double-wrap fixes. Flips REDs: `dotted_constructor_…`, FQ-D1, B4
   cycle, AL-3 span. 0568 (`__expr`) + 0576 ambiguous-type diagnostic fold in here.
2. **0581** (S87 residue) — shares same-named-ADT display surface + fixture family
   with bucket 2; land adjacent.
3. **0579** (doc/naming sweep) — mechanical.
4. **0580** (program.rs split) — **LAST**; rebases trivially (design signed off,
   `program-decomposition.md`). `/dev` tail: move + `public-api.txt` zero-diff +
   test-path citation fix (`#[cfg(test)] pub(crate) use` alias).

**W2 — Observability (bucket 1) — `src/agent`-local, INDEPENDENT (slot anytime):**
`/dev(src/agent)`: 6 log fields (F1–F6) + `question` required arg + probe channel
(E4 agent-gutter) + `scenario` env, against `repl/spec.md §17.20.3a–c`/§17.2.1 and
the `agent-context-tuning.md §4` metric acceptance. Threads C/D deferred.

**W3 — Display (int) — AFTER W1.1 (needs canonical keys):**
`/dev(src/ int)`: 0572 unified `:Type … ; meta` envelope + qual-name-not-`<closure>`,
0569 macro `; defmacro`, dotted-ctor listed-once, thread-B probe rendering — all E4
seam. Couples with bucket 2's double-listing.

**W4 — 0570 module visibility — AFTER MV-4 verify:**
`/stdlib` marks test submodules `(mod- test)`; `/dev` makes `/search` index + import
filter honor `mod-`. `/testing` MV twin.

**W5 — small/independent (`src/`, frontend):**
0573 `save.rs` → `type_def_info()` delegation (`/dev src/`, small; types landed).
0575 `fn` parse-error quality (`/dev` frontend).

**W6 — Polymorphic param-annotation fix (NEW, added P5; typecheck, independent):**
Implement implicit quantification of free type vars in `defn`/`fn` param annotations
(spec §3 — a free lowercase ident in a param annotation is a fresh var quantified at
the fn boundary, matching how inference already produces polymorphic schemes).
`/qa` — coverage-gap analysis + annotation-resolution variant×{pos,neg} matrix
{concrete app / free var / bare var} × {defn / fn / deftype field / let} + sweep for
other missing cells; `/design(typecheck)` — the annotation-resolver seam (if the fix
isn't a straight `/dev` read of §3); `/dev(typecheck)` — implement + unit tests;
`/testing` — the failing repro (`class=` resolution) + the matrix e2e; `/spec` — §3
example/annotation if needed. **NB: `/arch`/`/qa` pin the EXACT mechanism first**
(unimplemented vs narrower resolver bug) — investigate-before-fix.
Independent of dotted-ctor; slots into the typecheck serial chain (before or after
W1 — could run first while `/arch` re-rules W1's model).

**Cross-wave:** every `/dev` implementation wave is followed by narrow `/review`.
Public-API: only W1.1 moves the baseline (member_key/type_def_info already landed;
W1.1 adds nothing beyond the cache bump — a ResolutionGap variant only if the
contingency fires). W2/W3/W4/W5 = zero public-API.

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P2 | /arch | S109 draft scope | (shim §II.3) | (shim) | — Phase 2 review DONE: SIGN-OFF w/ 3 revisions (incorporated) |
| P3 | /spec | normative framings (§8.5.2 ctor, 0570, 0571) + 0575/0576 | (shim §II.3) | (shim) | — Phase 3 design (frame for user) |
| P3 | /arch | cranelisp-types interface change-set (member_key, type_def_info, 0567) | (shim §II.3) | (shim) | — DONE commit `9c69b203`: +2 additive API, 0567 RESOLVED, 0573 read-side ready, design-note `dotted-ctor-canonical-keys.md` (cache 16→17 + type_ctor_names Phase-5) |
| P3 | /arch (resume) | 0571 park/enqueue/resume mechanism review | (shim §II.3) | (shim) | — DONE: edifice EXISTS (S78/0268); real defect = slot-less-generic value-ref→codegen + FQ-cycle-misattrib + pool race; cure = unconditional member-absent gap; 10 §8.5.4 edges + A/B/C/D test rows |
| P3 | /spec (resume) | land settled text: items 1 (§8.5.2/§8.6.5/§6) + 4 (0575/0576) | (shim §II.3) | (shim) | — DONE: same-named ctors §8.5.2/§8.6.5 + §6.2.1/2/4 + EBNF; 0575 §4.5; 0576 §5.1.2; 0570 §8.2.3 clarify. Verifiers 0-dead. 0571 §8.5.4 HELD. 0575/0576/0570 FIXMEs stay open (/dev,/stdlib tails) |
| P3 | /design | typecheck — dotted-ctor inverted-model design | (shim §II.3) | (shim) | — DONE: `dotted-ctor-registration.md`; pattern=no-frontend-change; blast radius = exhaustiveness normalizer (`.` strip) + internal-ctor probe (IO Bind/Pure/Effect) — both same-change-set; double-listing flagged to /repl; zero pub-API |
| P3 | /spec (resume) | land 0571 §8.5.4 SHOULD→MUST + 10 edges | (shim §II.3) | (shim) | — DONE: §8.5.4 MUST + 10 numbered edges + §8.6.1 consistency; verifiers 0-dead. ALL 4 spec items landed (§8.5.2/§8.6.5/§6, §4.5/§5.1.2, §8.2.3, §8.5.4). FIXME tails open: 0575/0576/0570/0571 (/dev,/stdlib) |
| P3 | /repl | observability §17.20.3 + 0572/0569 display + thread B (E4 seam) | (shim §II.3) | (shim) | — DONE: §17.20.3a–c (F1–F6 + metric map), §17.2.1 probe channel, §1.1/§1.5/§17.19.2 unified envelope + qual-name-not-`<closure>`, §17.19.2a macro `; defmacro`, §17.19.2b/§3.3/§3.5 ctor listed-once. Repros owed to /testing (annotated, no FIXME) |
| P3 | /design (resume) | typecheck — 0578 traits.md rewrite + 0580 program.rs cut sign-off | (shim §II.3) | (shim) | — DONE: traits.md rewritten to as-built (0578 deleted); 9 doc-sprawl banners + CLAUDE.md doc-index; 0580 cut signed off (`program-decomposition.md`, 8 submodules <1200L, FIXME kept OPEN for /dev tail) |
| P3 | /qa | sprint-wide failing-test plan (exit gate) | (shim §II.3) | (shim) | — DONE: PLAN.md §S109 (AL/DC/SS/MV/OB/EV rows + arch A/B/C/D + BR-1/2 fail-on-revert + M1/M2/M3 matrices); C-class e2e-vs-unit enumerated; F6 resolved; `check-gate-leak` class added; risks.md S109-1..6. EXIT GATE MET |
| P5-S1 | /testing | sprint-wide QA-first failing tests (PLAN.md §S109) | (shim §II.3) | (shim) | — DONE: **MV-4 PASS** (mod- child-file works, W4 unblocked); 66 tests/10 files; suite 4432t/25f = 23 S109 RED + 2 carries, NO regressions; agent-lane 7 RED/3 GREEN; /dev-unit deferrals enumerated (OB-2, AL-8, BR-2, C1-gap-arms) |
| P5-S2 | /spec (resume) | §6.2.1 scrutinee-directed revision | (shim §II.3) | (shim) | — DONE: §6.2.1/§6.2.2 scrutinee-directed + unifying-rule frame; §8.6.5 clause; verifiers 0-dead |
| P5-S2 | /qa (resume) | S109 plan realign (DC reframe + AN-1..5 + W6 matrix) | (shim §II.3) | (shim) | — DONE: DC-11 new, DC-5 reframe, fixture constraint, AN-1..5, W6 §L matrix; new vocab `resolver-mirror` |
| P5-S2 | /testing (resume) | W1-prep tests (DC reframe + AN-1..5) | (shim §II.3) | (shim) | — DONE: +2 REDs (DC-11, AN-5); DC RED-for-right-reason (no W6 contamination); AN-1/3/4 GREEN pins hold; **AN-2 GREEN (patch-exposed fragility, reclassified)**; 27f = 25 S109 RED + 2 carries |
| P5-S2 | /dev (resume) | **W1 coordinate change-set** (typecheck+types+backend+int, 2 commits) | (shim §II.3) | (shim) | — **DONE, LANDED main** `3d449b7b`(readers,AN-5 flip,baseline-held) + `01c8062b`(writers,cache 16→17,scrutinee-directed). DC-1/3/4/6-11+BR-1/2+AN-1..5 GREEN. **+2 readers caught** (schema.rs::ctors_of, constructor_metas heap-leak). Zero pub-API |
| P5-S2 | /testing (resume) | DC-2 fixture fix | (shim §II.3) | (shim) | — DONE: fixture made coverage-correct (both types share Some+None); GREEN ×6 perms. **Suite 14f = 2 carries + 12 later-wave S109 (0571×5, 0575/6×2, 0569/72×2, 0570, 0573×2)**. W1 scope fully GREEN, no regressions |
| P5-S2 | /review | W1 change-set review (reader-audit completeness) | (shim §II.3) | (shim) | — **NOT CLEAN, 1 BLOCKER**: DC-11 scrutinee-directed = silent wrong-ctor codegen + nondeterminism (typecheck resolves canonically, backend re-resolves bare context-free). +I-1/I-2/I-3 Important. Repros in scratchpad. Same-sprint fix (W1.2) |
| P5-S2 | /arch (resume) | W1.2 DC-11 Blocker cure design | (shim §II.3) | (shim) | — DONE `d45e2cee`: cure (a′) resolved-ctor rides mono node → backend CONSUMES tc resolution (one pattern resolver, loud-miss P18); design §10. Landed: `bare_member_name` + depth guard. I-1 folded (bare_member_name both sides), debug-asserts YES, cache 17→18. /qa tag-order matrix §10.9 |
| P5-S2 | /qa (resume) | W1.2 tag-order matrix rows | (shim §II.3) | (shim) | — DONE: PLAN §D.3 — DC-12 (differing-layout twins both orders), DC-13 (xmod nondeterminism guard), DC-14 (warm-cache 17→18), BU-1/BU-2 (/dev unit pins) |
| P5-S2 | /testing (resume) | W1.2 Blocker guards DC-12/13/14 | (shim §II.3) | (shim) | — DONE: all 3 RED for right reason (DC-13 nondeterminism reproduced 1/7/1, 1/1/7); W1 rows stay GREEN; suite 14→17 |
| P5-S2 | /dev (resume) | **W1.2 §10 Blocker cure** (typecheck+types+backend) | (shim §II.3) | (shim) | — **DONE, LANDED `c1e399e4`**: resolved-ctor rides mono node → keyed read (one deterministic pattern resolver). DC-12/13/14 GREEN (DC-13 3×→7 deterministic); W1 rows hold; BU-1/2/3. Found+fixed drained-sidecar seam bug. FIXME 0584→/arch (lenient-body None-arm ratify). Cache 17→18 |
| P5-S2 | /sprint | commit S109 durable record (I-3 close) | — | — | — `a919bfd8`: 50 files (spec/design/test/plan/audit/fixmes); closes the fix-without-committed-tests inversion; later-wave REDs = known-defect guards |
| P5-S2 | /dev (resume) | **0571 FQ-reference cluster** (typecheck+int) | (shim §II.3) | (shim) | — **DONE `35153cf8`**: FQ-D1 value-pos-generic mint (Let/ParBind) + FQ-D2 introspection-path + B4/B5 member-absent-unconditional-gap→int-decides-cycle + AL-3 reference-span. All 5 guards + bonus EV-1 GREEN; mode-parity verified; NO backend resolution added; zero pub-API. Suite 8f |
| P5-S2 | /dev (resume) | 0573 product-deftype persistence | (shim §II.3) | (shim) | — **DONE `e22763ca`**: save.rs one-line `type_def_info()` delegation; both rows GREEN; reload + --run/--link parity. Suite 6f. (0569/0572 display rows already GREEN) |
| P5-S2 | /dev (resume) | 0575/0576 error-quality diagnostics | (shim §II.3) | (shim) | — **DONE `5764b538`**: fn single-arity parse msg (§4.5) + multi-arity defn names clause/param (§5.1.2) + 0568 `__expr` guarded same path; both rows GREEN + unit pins. Suite 4f = 0570×2 + 2 carries |
| P5-S2 | /testing | 0571.2 review-finding negatives (B1/I1/I2) | (shim §II.3) | (shim) | — DONE: 5 negatives RED for right reason (B1 mode-divergence, I1 failed-reset false-no-member, I2×3 if/match/vec check-gate-leak). Suite 9f (concurrent landings dropped 17→9) |
| P5-S2 | /dev (resume) | **0571.2 fix pass** (typecheck+int) | (shim §II.3) | (shim) | — B1 visibility gate + I1 failed-reset predicate + I2 uniform value-position mint + I3 Failed fail-fast + I4 comments/dedup + M2 cycle span; flips 5 negatives |
| — | — | later-wave REDs remaining | — | — | 0570 (mod- honor, W4), 0569 (search macro `; defmacro` row, W3) still RED |
| P5-S2 | /review | 0571 scheduler gap-arm review | (shim §II.3) | (shim) | — **NOT CLEAN: 1 Blocker + 4 Important** (see 0571 REVIEW note). Confirmed: no lost-wakeup re-open, cycle determinism, 0513 preserved, no backend resolution. Blocker = private-FQ-display visibility bypass (mode-divergence) → 0571.2 fix pass |
| P5-S2 | /dev | W1.1a typecheck — bucket 2 dotted-ctor capability | (shim §II.3) | (shim) | — **REVERTED (blocked)**: mechanism works but canonical-key model has ~54 int-side regressions (display/quasiquote→prelude cascade/bootstrap-seeded-ctor split); work preserved as patch. 3 escalations (see W1.1a BLOCKER note) |
| P5-S2 | /arch (resume) | W1 model re-ruling ((b) coordinate) + #2 ordering + per-regression verify | (shim §II.3) | (shim) | — **DONE**: measured 73 regs (not 54); ROOT = ONE backend site `lookup_constructor` (context.rs:146) one-hop bare-key (NOT quasiquote/seeded); **found SILENT soundness bug** (cross-module nullary ctor → closure-alloc vs iconst-tag, 2 backend resolvers disagree); coordinate design in `dotted-ctor-canonical-keys.md`; **#2 ordering YES tractable**; accessor-bug folds into W1 commit-1; FIXME 0582→/design |

## Notes

- **Phase 1 (2026-07-13):** scope drafted from the S108-Inc3-6a testing findings
  (0567–0573, 0575–0577) + S108 typecheck-audit disposition. Three genuine gates
  resolved with user: dotted-ctor → **full-capability fix** (R-3 declined); audit →
  **all four** R-1/2/4/5 accepted; breadth → **Broad**.
- **Known RED at entry:** ownership_reuse (0528, carry), deftype_ctor_trailing
  (S107, carry), dotted-ctor (now IN SCOPE to fix). No genuine regressions.
- **Size honesty:** this is a large sprint. Per "no defer for size; decompose into
  waves," Phase 4 splits it; scope is not shrunk. Observability (bucket 1) is the
  lead wave and is largely `src/agent`-local (low cross-crate risk).
- **Phase 3 /qa inputs (for the exit-gate dispatch):** (a) `/repl` flagged that
  `agent-context-tuning.md §4` has NO standalone step-accounting metric — `/qa` must
  either add one or confirm F6 folds into Probes-per-submit + Give-up rate. (b) `/qa`
  plan must ROW every landed spec-MUST (§8.5.4 ten edges, §8.5.2/§8.6.5/§6 ctor rules,
  §4.5/§5.1.2, §8.2.3) AND fold arch's 0571 A/B/C/D + `/design`'s two blast-radius
  negatives (exhaustiveness `.`-strip, IO-internal-ctor exclusion — guards that FAIL
  on revert). (c) coverage-by-definition-variants MATRIX (variant×{pos,neg}) as an
  explicit table (dotted-ctor positions; §8.5.4 modes×positions×kinds). (d) the
  C-class scheduler race: `/qa` must ENUMERATE e2e-vs-unit per case (arch's
  scheduler-seam unit fallback), not hand-wave.
- **Phase 3 (2026-07-13):** Normative rulings resolved with user (see Rulings §):
  same-named ctors = §8.6.5 coexist (confirmed); 0570 = enforce existing `mod-`
  (reframed from normative-Q to /stdlib+/dev conformance); 0571 = A + scheduler
  park/enqueue/resume mechanism (needs dedicated arch review + rigorous testing);
  0575/0576 wording confirmed. `/arch` types change-set LANDED (`9c69b203`): 0567
  RESOLVED, `member_key` + `type_def_info` additive, 0573 read-side ready, Phase-5
  design note `design/arch/dotted-ctor-canonical-keys.md` (Obligation A
  type_ctor_names walk + Obligation B CACHE_SCHEMA_VERSION 16→17, both ride the
  adt.rs registration change-set). **Phase-5 carry-notes from arch:** (a) a 4th
  hand-rolled member-key site `infer.rs:235` rides the `member_key` sweep; (b) stale
  0567 comment `src/repl.rs:728` reword in the int-touching wave.
- **Phase 2 (2026-07-13):** `/arch` SIGN-OFF with 3 revisions (all incorporated):
  0567 →/arch; bucket-2 mechanism named (field inverted-model mirror, MEDIUM,
  resolve-only forbidden as Principle-8 interim) + pattern-position added to scope;
  0572/thread-B pinned to the E4 styled seam. Bucket-2 gained **pattern position** —
  a real scope addition (values must be matchable, not just constructible). Three
  `cranelisp-types` items consolidate into one Phase-3 `/arch` change-set. Audit
  rotation → `src/`.

## W1.1a BLOCKER (Phase 5, 2026-07-13) — dotted-ctor registration model needs re-ruling

`/dev` implemented the arch-ruled canonical-key-is-real/bare-alias model; mechanism
GREEN for well-formed cases (DC-1/3/4/6/7/9, BR-2 + unit tests), but **reverted** on
3 issues (work preserved: patch at scratchpad `dotted-ctor-typecheck.patch`):

1. **Int-side blast radius (~54 regressions) → `/arch` RE-RULING.** Making bare ctor
   keys aliases breaks pervasive `src/` int consumers: ADT value display (`(Cons 5
   Nil)`→bare `Lst.Cons`, fields dropped); **resolution of the seeded syntax-repr
   ctors (`macros/SCons`/`macros/Sexp*`) that quasiquote DESUGARS INTO** — NOT
   quasiquote inspecting ctor shape (quasiquote is Sexp→Sexp syntactic; user-
   verified 2026-07-13). The `list` macro's emitted code fails to resolve those
   seeded ctors → prelude circular-dep cascade drops list/vec/do/pure/cond/when/
   case/def. Also cross-module ctor resolution, introspection/search. **Root:**
   typecheck canonical-keys USER ctors but int `bootstrap.rs::register_synth_adt`
   keeps SEEDED ctors (Option/Result/IO, `macros/S*`) bare-keyed → inconsistent split.
   Design §6 blast-radius table was empirically wrong (ctors, unlike accessors, are
   seeded + emitted by quasiquote desugaring + displayed as values + pervasively
   imported). **NB (investigate-before-fix): `/arch` must pin the EXACT failing
   resolution per regression, not inherit `/dev`'s labels.**
   Two paths for `/arch`: (a) INVERT — keep bare real, add canonical alias, only
   CONTESTED names poison (shrinks blast radius; the P2-rejected resolver-only path
   didn't weigh this cost); (b) COORDINATE — keep canonical-real, expand W1 to a
   typecheck+int change-set (fix display/quasiquote/bootstrap-seeded consistency).
   **RULED (user, P5): (b) COORDINATE** — simplicity + consistency (one uniform rule
   across all ctors; "100 such decisions would be chaos"). Canonical-real stays;
   W1.1a expands to a coordinated typecheck+int change-set: fix `display.rs`,
   quasiquote/macro construction, introspection/search/`/list`, cross-module
   resolution, AND make `bootstrap.rs::register_synth_adt` seed ctors under CANONICAL
   keys (the consistency fix). `/arch` STILL REVIEWS the expanded plan + corrects
   design `dotted-ctor-registration.md §6` (blast-radius table). Likely folds in the
   latent field-accessor same-cluster `--run` fix (same resolver path).
2. **Pattern-position bare contested ctor → RULED A (user, P5): SCRUTINEE-DIRECTED.**
   Bare `(Some x)` in `(match m …)` resolves against the scrutinee's type
   (`m: Maybe` → `Maybe.Some`); poisons ONLY when the scrutinee type can't
   disambiguate (polymorphic scrutinee). One context-driven rule (value=no-context→
   poison; pattern=scrutinee-context→resolve); patterns already resolve against the
   scrutinee, so this is the natural extension, not a carve-out. Matches Rust/ML/HS.
   **CONTINGENT: `/arch` MUST confirm the scrutinee-type-availability ORDERING is
   tractable** (scrutinee type pinned before contested-pattern resolution runs — the
   same inference-order fragility class `/dev` hit in W1.1a) BEFORE we commit; if not
   tractable, revisit. Consequences: `/spec` revises §6.2.1 (flat-poison → scrutinee-
   directed + poison-when-unknown); `/testing` — DC-8/DC-2 flip to expect resolution,
   DC-5 reframed to "poison only when scrutinee type unknown."
3. **Polymorphic-param-annotation defect → RULED (user, P5): FIX in its own wave
   THIS sprint (W6).** VERIFIED live 2026-07-13 (`/sprint` REPL): `(defn f [:(Box a) b])`
   and bare `(defn ident [:a x] x)` → `unknown type 'a' (from module '')`; `deftype
   (Box a)` and concrete `:(Box Int)` work. So **free type vars in defn/fn PARAM
   annotations are not recognised as implicitly-quantified vars** (spec §3 says they
   MUST be) — a whole annotation-surface slice unimplemented. "Can't have parts of
   the language unimplemented" (user). DC-2/DC-5/BR-1 rewrite to concrete/inferred to
   unblock W1's dotted-ctor tests; the poly-annotation FIX is W6.
   **QA COVERAGE FINDING (user, P5):** the deeper issue is WHY this shipped untested —
   annotation resolution is a coverage-by-definition-variants family {concrete app /
   free type var / bare var} × {defn param / fn param / deftype field / let}; the
   free-type-var cell was never a test, letting the codepath stay unimplemented. `/qa`
   builds the variant×{pos,neg} matrix (W6) AND sweeps for OTHER missing cells in the
   same family (are there further unimplemented-but-untested annotation positions?).

**Bonus find:** the already-landed **field-accessor** feature has a latent
same-cluster `--run` bug (bare accessor `v` never worked same-cluster; only
cross-cluster REPL / cross-module was tested) — `/dev`'s staging fix surfaced it.

**W1 chain PAUSED** pending #1 (/arch) + #2 (user). W2 observability is independent
(could proceed, but held for serial-source discipline).

### W1.1a RESOLUTION (arch re-ruling DONE, 2026-07-13)
- **#1 (b) coordinate design landed** in `design/arch/dotted-ctor-canonical-keys.md`:
  uniform canonical keying (adt.rs + `bootstrap.rs::register_synth_adt` + IO.Bind;
  product ctors keep type-name key). Readers: **backend `lookup_constructor`
  COLLAPSES onto the one `resolve_driven` multi-hop driver** (the one-hop copy at
  context.rs:146 IS the P7 duplication + the soundness bug — do not widen it in
  place); `display.rs::ctor_field_types` probes `member_key` first;
  `imports.rs::collect_member_glob` installs bare-alias edges too. **Staging primitive
  fix (§3.5):** amend types `chain_follow_committed` so same-module `Import` hops use
  the caller's first-hop view (staging∪live) — this also fixes the latent
  field-accessor same-cluster `--run` bug (folds into W1 commit-1).
- **Structure: ONE `/dev` (typecheck+types+backend+int), TWO commits** — (1)
  reader-widening (behaviour-invariant, MUST hold the 25-fail baseline, revertable);
  (2) writer-flip + `CACHE_SCHEMA_VERSION` 16→17 + fixture-assertion updates + RED
  flips. Ordering structurally prevents the W1.1a failure mode. Zero new public-API.
- **#2 ordering: YES tractable** (`infer_match` infers scrutinee before arms, already
  passes `scrutinee_ty` to `check_constructor_pattern`; the W1.1a "fragility" was the
  staging axis, cured at the primitive). **Contingency CLEARED** — scrutinee-directed
  is a go; `/spec` §6.2.1 revision unblocked.
- **Cross-module nullary "soundness bug" — RECLASSIFIED (P5, /testing evidence):**
  NOT pre-existing. On clean HEAD the one-hop `lookup_constructor` miss is rescued by
  the step-3 global bare-name fallback → correct value (/testing probed 10+ shapes,
  all GREEN). Arch saw the wrong value only WITH `/dev`'s patch applied (key moved →
  BOTH one-hop and bare-fallback miss → closure path). So it is a **latent fragility
  (two resolvers) the naive key-flip would EXPOSE**, not a live bug — which VINDICATES
  the two-commit structure (commit-1 reader-collapse eliminates it before commit-2
  moves keys). **AN-2 = GREEN invariance pin** (must hold through both commits), not a
  RED repro. `resolver-mirror` collapse in commit-1 is fragility-elimination, not a
  bug fix.
- **FIXME 0582** → `/design`: correct `dotted-ctor-registration.md §6` blast-radius
  table (the "tag dispatch unaffected" row wrong; display/member-glob/seeded-writers
  rows missing). Audit lesson: a keying change's blast radius = every crate's raw
  `table.get` probes, not just the owning crate.

**W1 redispatch plan:** `/spec` §6.2.1 (scrutinee-directed) → `/qa`+`/testing` update
DC-8/DC-2 (flip to resolve), DC-5 (reframe), concrete-ize DC-2/DC-5/BR-1 (unblock from
W6 poly-annotation defect), add the 73-regression-class acceptance negatives + the
accessor `--run` twin → `/design` 0582 → **W1 `/dev`** (coordinate change-set, 2
commits, from the preserved patch) → `/review`.

## W1 /review findings (2026-07-13) — NOT CLEAN, 1 Blocker (same-sprint fix)

`/review` swept ~120 ctor-key read sites. Audited table-probe readers canonical-safe
EXCEPT:

- **BLOCKER — DC-11 scrutinee-directed patterns are a SILENT WRONG-CTOR soundness
  defect at the typecheck↔backend seam.** Typecheck (infer.rs:1016-1060) accepts bare
  `(Some x)` scrutinee-directed + resolves canonically, BUT that resolution never
  reaches the backend: the `pattern_ctors` sidecar (cranelisp-types check.rs:76) is
  populated and consumed by NOTHING; the recorded FQSymbol carries the BARE name.
  Backend `match_codegen.rs:227` re-resolves the bare name context-free via
  `resolve_driven`'s global fallback, which iterates a DashMap in ARBITRARY ORDER →
  lands on the wrong module's same-named ctor (wrong tag) → runtime `match failed` on a
  typechecked-total match + **run-to-run NONDETERMINISM** (repros confirmed:
  scratchpad `repro/main.cl` exit 1 deterministic; `xmod.cl` exit 1/7/7 across 3 runs).
  Committed DC-11/DC-6 e2es are green only by tag-layout COINCIDENCE — the acceptance
  matrix is missing the **tag-order-differing** negative (coverage-by-variants:
  variant axis = ctor declaration order across candidate modules). Same mirror class
  (two resolvers disagree) the change-set cured INSIDE the backend, re-emerged one seam
  up via commit-2's DC-11 arm. **Cure:** sidecar carries the CANONICAL `member_key`
  symbol + `match_codegen` consumes it (or typecheck rewrites pattern ctor names to
  `module/Type.Ctor` before mono). → `/arch` (sidecar contract) + `/dev` (backend+tc) +
  `/qa` (tag-order matrix) + `/testing` (repro guards). **W1 NOT done until fixed.**
- **I-1** (Important) — `let_if.rs::collect_module_constructors` reads storage keys as
  source names → sum ctors drop from spark-exclusion (`sparkability.rs:291`); env-gated
  `/qa` comparison row skewed. Another mirror-class unaudited reader. → `/dev`.
- **I-2** (Important, NORMATIVE) — `adt.rs:470` `None => {}` collision arm silently
  REVERSES pre-flip clobber (defn-over-ctor-bare-name now preserves prior binding, was
  clobber); §8.6.4 suggests a CONFLICT ERROR, neither outcome spec-cited/tested. →
  `/spec` (frames for USER) + `/qa` row.
- **I-3** (Important, PROCESS) — the entire S109 test suite (~2,500 lines/15 files) is
  UNCOMMITTED working-tree state; W1's commits cite acceptance against sources not in
  HEAD (fix-without-committed-tests inversion). → commit the suite as durable record
  (after the Blocker fix + tag-order negative land).
- **MINORs**: `resolve_driven` omits design-§3.1 canonical-key probe (reconcile in
  design at archive); silent-skip enumerators want a Principle-18 debug-assert;
  `chain_follow_committed` new self-recursive arm lacks a depth guard.

**Verified GREEN by /review:** P7 duplication cure (one-hop body deleted, no dormant
copy); DC-11 typecheck-half correct per §6.2.1; the 2 mid-work fixes are root fixes;
two-commit discipline honored; public-API zero movement; writer uniformity (§1).

## 0571 REVIEW findings (2026-07-14) — NOT CLEAN; 0571.2 fix pass owed

`/review` confirmed the gap-arm mechanism is sound (no S93 re-open, cycle determinism,
0513 preserved, mode parity on the compile path, no backend resolution) — but found:

- **B1 (BLOCKER) — private-FQ-display visibility bypass (mode-divergence + §8.7.3
  violation).** 0571's D2 introspection arm (`src/eval.rs:586-598`) raw-probes the
  table with NO `is_public()` gate → a private `defn-` member displays via the REPL
  introspection intercept instead of erroring; `--run` errors correctly. Also a NEW
  raw-probe resolution-mirror site (S110-boundary class). → `/dev` (int) + `/qa` neg
  twin (no private-FQ negative test exists).
- **I1 — "no member Y" fires for a failed-then-reset module** — masks the real load
  failure + wedges recovery. `fq_module_is_loaded` counts a reset module as loaded
  (`is_typechecked` returns true for a forgotten module; the empty seeded table is
  never removed on failure). → `/dev` (int) + `/testing` repro.
- **I2 — value-position mint covers only Apply-arg + Let/ParBind; concrete generic
  refs in if/match/vector positions STILL leak to codegen** (`((if c gcount gother)
  […])`). **3rd recurrence** (0374 HOF → 0488 imported → 0571 let-value) of the
  "monomorphise-uniformly-across-value-positions" class; the uniform fix (verdict on
  every non-callee `Var`) exists 20 lines away. → `/dev` uniform collect + **`/arch`
  class escalation (FIXME 0585)** + `/qa` if/match/vec matrix cells.
- **I3 — `block_for_typecheck` lacks a Failed fail-fast** — a waiter registered on an
  already-Failed dep becomes a zombie; the reshape widened the gap set routed here.
  Mirror `await_signature_barrier`'s fail-fast. → `/dev` (int).
- **I4 — stale contradictory comments at the 0513 seam + `phantom_member_diagnostic`
  (0490) is a 2nd int-side site authoring "module X has no member Y" (mirror); no
  design doc records the new gap-arm contract.** → `/dev` (comment cure + consolidate
  to one diagnostic site) + `/design` (record the contract).
- **Minors**: M2 cycle error still `Span::SYNTHETIC` (AL-3's own headline case!);
  M3 5×-dup `ModuleFailed` construction; M4 partial ref-span scan + wasted park IO;
  M5 `finalize_cluster` ~127L over budget.

**0571.2 plan:** `/dev` fix pass (B1 + I1 + I2-uniform + I3 + I4 + M2) AFTER the
0575/0576 diagnostics wave frees the source token → `/testing` negatives (B1 private-FQ,
I1 failed-reset-retry, I2 if/match/vec) → re-`/review`. FIXME 0585 → `/arch` (I2 class).
Note: B1/M1/I4 are the resolution-mirror class = the S110 centrepiece re-instantiated
under time pressure — reinforces 0583.

## Outcome (Phase 7)

### Delivered
- {tbd}

### Deferred (with rationale)
- {tbd}

### Findings (record in FIXMEs if not already)
- **S110 CENTREPIECE + `/audit` calibration miss (user, P5) → FIXME 0583.** The
  backend runs a full name resolver (10 `resolve_*` + the arbitrary-order
  `resolve_driven` global scan) instead of receiving FQ symbols from typecheck — a
  bounded-context boundary violation and the root of the mirror class that recurred
  **3× in S109** (backend one-hop vs multi-hop; nullary closure/tag split; DC-11
  patterns). Tractable (typecheck already computes the FQ; the fix is plumbing it to
  the mono node + keyed reads, per the `§10` template). **`/audit` MISSED this** — no
  whole-context assessment flagged resolution living in the wrong crate; add a
  "bounded-context responsibility boundary" lens + pull backend/resolution forward in
  the audit rotation. User directive: **backend-pure-consumer — typecheck emits FQ
  SYMBOLS and FQ TYPES, zero backend name/type resolution — is the S110 centrepiece**
  (both axes: `resolve_driven` symbol scan AND bare-type-name keying for
  layout/tags/schema/drop-glue; `FQSymbol`/`FQTypeName` the only forms backend sees).
- The mirror class ("two resolvers, one name") is a recurring-defect-class signal for
  `/arch` (Phase-7 principles review): the durable cure is architectural (one resolver,
  typecheck-side), not per-instance. `/review` caught the DC-11 instance; the audit
  should have caught the class.
- Process (I-3): W1's code committed ahead of its acceptance tests (uncommitted
  working-tree) — the S109 suite must be committed as the durable record once the
  W1.2 Blocker negative is green.
