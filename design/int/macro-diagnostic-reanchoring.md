# Macro-route diagnostic re-anchoring — synthetic-span errors relocate to the origin form (S113 W4, FIXME 0650)

> Subordinate topic doc, cited from `design/int/int.md`. Owned by `/design`(int).
> Authored S113 Phase 3 for SPRINT.md §Scope-D + the `/arch` ruling recorded in
> `design/arch/fixmes/0650-*.md`. **LANDED S113 W4** (`/dev`(src/), reviewed
> APPROVE): `process_form::reanchor_expansion_diagnostic`, e2e cell
> `macro_route_qualified_head_reject_span_at_written_form` GREEN. The paired
> frontend reject is `design/frontend/binder-head-reject.md` (landed W3,
> inert-safe first).

> **As-built note (settled state).** The seam landed at
> **`src/process_form.rs:784` (`reanchor_expansion_diagnostic`)**, applied at the
> per-form build site (`:936`, `Err(reanchor_expansion_diagnostic(e, sexp.span(),
> sexp))`), **NOT** at `worker::build_program_compat` (`worker.rs:73`) as §2 below
> designed. The relocation belongs with the caller that holds the origin form —
> `process_form` — rather than the `build_forms` wrapper; the design intent
> (synthetic-location predicate, append-provenance, pure transform) is unchanged.
> §2's `worker.rs:73` reference is the design-time seam candidate; read
> `process_form.rs:784/:936` as the live site. Unit tier landed at
> `process_form/tests.rs:167/:933`.

> **Residual — SCHEDULED S114 Track C (design §2.1 below).** The W4 seam covers
> **frontend** diagnostics from `build_form(s)` over expansion output.
> **Typecheck** errors over macro-expansion output — surfaced via
> `check_program_compat` at finalize (`process_form.rs:468`) — still carry
> synthetic spans and reach the user as `def`/`const`-route diagnostics pointing
> at no source byte. The S114 extension applies the **same** re-anchor transform
> at that second application site: identical synthetic-location predicate,
> identical origin-span + `in expansion of …` treatment, **no new mechanism**.
> Designed in §2.1.

## 1. The problem — a correct reject with a useless location

The W3 frontend binder-head reject (`reject_qualified_binder_head`) fires
correctly on a qualified head reached **via macro expansion** — `def`/`const`
(stdlib macros) or any user inline `defmacro` whose expansion emits a qualified
`defn`/`defmacro` head. Correctness is preserved: `(def fmt/x 1)` rejects. But the
diagnostic **location and shown name degrade to synthetic values**, because int's
macro-expansion pipeline discards all source provenance from macro output:

- `src/marshal.rs:62` — every Sexp a macro returns is unmarshalled with
  `Span::SYNTHETIC` (`= Span { start: 0, end: 0 }`).
- `src/expander.rs` `rewrite_spans_unique` — assigns each expansion node a **fresh
  unique synthetic span** in the ≥ 1_000_000 band (span-uniqueness is a landed
  invariant for the `backend-keyed-consumer.md` span-keyed carriers; preserving
  real spans through the marshal boundary is REJECTED — it would collide with that
  invariant, `binder-head-reject.md` §4.1).

So the reject on the synthesized `(defn fmt/x-def …)` head points at a span that
maps to **no source byte**, and for `def` (which mangles `~impl-name = fmt/x-def`)
names the mangled synthesized head, not the written `fmt/x`. Native forms are
unaffected (a directly-written `(defn fmt/foo …)` keeps its real reader span).
Spec `05-definitions.md` §5 + `tests/plan/s113-test-plan.md` BD-M2/M3 carry a hard
MUST: the diagnostic span MUST point at the **user's written form**.

## 2. The seam — re-anchor at the `build_form`/`build_forms` drive site

int already threads the original call's real span as `origin_span` **into**
expansion for diagnostics raised *during* expansion (FIXME 0485;
`src/expander.rs:707` doc, `call_span = origin_span.unwrap_or(span)`). The binder
reject fires **after** expansion returns — at the frontend fold, when int drives
`build_forms` over the expanded sexps. That drive site is
**`worker::build_program_compat` (`src/worker.rs:73`)**, called from
`process_cluster_once` where the pre-expansion cluster source + the origin form's
real span are in hand.

**The seam:** when int drives `build_form`/`build_forms` on macro-expansion
output and it returns an error whose `location` is **synthetic**, re-anchor that
error's `location` to the **origin form's span** (the span int holds for the
pre-expansion form) and append expansion context to the message.

This is diagnostic-location *enrichment* at the layer that owns the provenance —
NOT a second reject seam. The reject stays single-sourced in frontend (Principle
7 / P19). Span-uniqueness stays intact: macro output keeps its unique synthetic
spans for the carriers; only the one surfaced diagnostic's `location` is
rewritten.

## 2.1 The finalize/typecheck-error extension (S114 Track C — the def/const path)

The W4 seam fires only where int drives `build_form(s)` over expansion output. A
**typecheck** error over macro-expansion output takes a different route: it is
surfaced by `check_program_compat` at the cluster **finalize** step
(`src/process_form.rs:468`, `let (maybe_gap, …) = check_program_compat(…)` over
`final_working`), which typechecks the fully-expanded cluster. A `def`/`const`
(stdlib macros) whose expansion typechecks with an error — e.g. a type mismatch in
the synthesized body — surfaces that error carrying the macro output's
**synthetic** span (`Span::SYNTHETIC` from marshal, or the `rewrite_spans_unique`
≥ 1M band), so the user sees a diagnostic anchored at no source byte, with no
`in expansion of …` provenance.

**The extension is a second APPLICATION SITE of the existing transform, not a new
mechanism.** `reanchor_expansion_diagnostic` (`process_form.rs:784`) is already a
pure `(error, origin_span, source_text) → error` function (§6): synthetic-location
predicate in, origin-span + `in expansion of …` suffix out, native-form errors
passed through unchanged. The S114 work wraps the finalize-path typecheck error in
the **same** call, at the finalize site that holds the same provenance the W4 site
holds — the pre-expansion cluster source text and each origin form's real span.

**Design constraints (unchanged from §3–§6, restated for the new site):**

- **Key on the synthetic-location predicate, never the error class** (§3). The
  finalize path yields *typecheck* errors, a different class from the frontend
  binder reject — which is exactly why class-sniffing would fail and the
  structural "location maps to no source byte in the cluster's source text"
  predicate is the right and only key. Re-anchoring is strictly better for every
  finalize-path error class (any typecheck error over macro output gets a located
  diagnostic for free), so the predicate closes the whole family here too.
- **The origin form for a multi-form cluster.** Finalize typechecks the whole
  `final_working` cluster; a surfaced error must re-anchor to the **origin form
  whose expansion produced the erroring node**, not blanket-anchor to the cluster
  head. The finalize site holds the pre-expansion cluster forms; the origin span
  is the pre-expansion form whose real byte extent the erroring node's provenance
  belongs to — the same "outside the origin form's real byte range" test §3 uses,
  applied per-form. If the error's synthetic node cannot be attributed to a single
  origin form (rare — a cluster-level check with no single culprit), the **landed**
  fallback is the **FIRST origin form's span** (not "the cluster's own source
  span" as this doc originally read — aligned to as-built S115, FIXME 0699 item 4;
  pinned by `process_form/tests.rs::reanchor_finalize_multi_form_falls_back_to_first_origin`,
  `:1064`) — a real, if coarse, location always beats a no-source-byte location.
- **Append provenance, never re-phrase** (§4) — the typecheck message stays
  single-sourced in `cranelisp-typecheck`; int adds `  in expansion of <written
  form>` naming the origin form it holds. Never reconstruct or second-guess the
  typecheck text (Principle 7).
- **Pure + unit-testable** (§6) — the extension needs no new transform, so the
  existing unit tier (`process_form/tests.rs:167/:933`) extends with one cell: a
  finalize-shaped error carrying a synthetic `location` + an origin span + source
  text ⇒ re-anchored location + `in expansion of …` suffix; a native finalize
  error ⇒ passes through unchanged.

**Do NOT** preserve real spans through the marshal boundary to avoid the problem —
that is REJECTED (§1, §8): it collides with the span-uniqueness invariant the
`backend-keyed-consumer.md` carriers depend on. The re-anchor-at-the-owning-layer
model is the settled shape for both sites.

**Testability.** Whether the def/const finalize error is reachable end-to-end (a
`--run`/REPL cell producing a synthetic-span typecheck error over `def`/`const`
output) is `/qa`+`/testing`'s to pin; the unit tier is `/dev`'s at the finalize
application site.

## 3. The binding arch pin — key on the SYNTHETIC-LOCATION predicate, never the error class

**`/arch` ruling (recorded in 0650, confirmed here):** do NOT key the re-anchor on
recognizing "a binder-reject error" — error-class sniffing (worst form: message
string-matching) is fragile and a **`/review` REJECT**. Key it on the
**synthetic-location predicate**:

```
any error produced by build_form(s) over macro-expansion output
whose `location` maps to no source byte in the cluster's source text
    ⇒ re-anchor `location` to the origin form's span.
```

A synthetic span maps to no source byte and is **never** useful to a user, so
re-anchoring is strictly better for **every** error class — this closes the whole
family (any future frontend reject on macro output gets a located diagnostic for
free), not just the binder reject. The predicate is structural, not classificatory.

**Predicate mechanics.** There are two synthetic-span flavours to catch, and both
map to no real byte:

- `Span::SYNTHETIC` = `(0, 0)` (marshal output), and any zero-width `start == end`;
- the `rewrite_spans_unique` unique band (`start`/`end` ≥ the ≥ 1_000_000 offsets,
  beyond any real source length).

The robust test the seam owns (it holds the cluster's source text): the error's
`location` is synthetic iff its byte range does **not** fall within the
pre-expansion form's real byte range in that source text (`start == end`, or
`end > source_len`, or `[start,end)` outside the origin form's extent). Prefer
this "outside the real source extent" test over hard-coding the 1M constant, so a
future change to the synthetic band cannot silently defeat the seam. (If a
`Span::is_synthetic()` predicate is added to `cranelisp-types` for this, that is a
types touch → FIXME `target: /arch`; the int-local "outside source extent" test
needs no types change and is preferred for W4.)

## 4. Message treatment — append provenance, never re-phrase

**Prefer appending expansion context over rewriting the frontend message** — the
frontend error text stays single-sourced (Principle 7); int adds provenance, never
re-phrases. Shape:

```
<frontend reject message, verbatim>
  in expansion of `(def fmt/x …)`
```

naming the **written** head/form (the origin form int holds), so the user sees
both the real rule (frontend's text) and where they typed the offending form. int
never reconstructs or second-guesses the frontend message.

## 5. Sequencing (per the 0613 quote-shield precedent)

The frontend reject (W3) is **inert-safe** without this seam — a qualified
macro-route head still rejects (correctness), only its location/name degrade. So
the frontend reject lands W3 ahead of the int seam; this re-anchoring lands **W4**.
The BD-M2/M3 e2e (degenerate-span assertion) stays **RED until this seam lands**
and is the durable trigger that keeps it honest. Delete FIXME 0650 when the seam
lands and BD-M2/M3 flip green.

## 6. Testability (Principle 5)

The re-anchor is a pure `(error, origin_span, source_text) → error` transform,
unit-testable with no session: feed an error carrying a synthetic `location` +
an origin span + source text ⇒ assert the returned error's `location` equals the
origin span and the message carries the `in expansion of …` suffix; feed a
NATIVE-form error (real span within the source extent) ⇒ assert it passes through
**unchanged** (the predicate must not touch already-located diagnostics). The
e2e/provenance-through-expansion assertion (BD-M2/M3) is `/qa`+`/testing`'s.

## 7. Principles cited

- **Principle 7 / Principle 19** — the reject stays single-sourced in frontend; int
  enriches location, never adds a second reject seam or a name-privileged
  special-case.
- **Principle 18** — the re-anchor keys on the structural synthetic-location
  predicate (where the provenance defect lives), not on classifying the error.
- **Principle 26** — re-anchor to the settled origin span int already holds, never
  re-derive a location from the synthesized form.

## 8. Cross-references

- `design/frontend/binder-head-reject.md` §4 — the paired frontend reject + the
  §4.1 rejected deep fixes (span-preservation breaks span-uniqueness; per-form
  special-casing violates P19).
- `design/int/quote-shield.md` — the 0613 frontend-fold + int-shield pairing this
  mirrors (one logical wave, two `/dev` surfaces).
- `design/arch/backend-keyed-consumer.md` §1.1 — the span-uniqueness/carrier
  invariant that forbids preserving real spans through marshal.
- `src/worker.rs:73` (`build_program_compat`) + `src/expander.rs:707`
  (`origin_span` / FIXME 0485 discipline) — the seam + the provenance int holds.
- `src/marshal.rs:62` + `src/expander.rs` `rewrite_spans_unique` — the
  synthetic-span sources (§1).
- `design/arch/fixmes/0650-*.md` — the `/arch` ruling this designs against.
- `tests/plan/s113-test-plan.md` BD-M2/M3 — the durable-trigger e2e.
