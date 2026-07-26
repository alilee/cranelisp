---
number: 0915
target: /design (backend)
filed_by: /repl
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-backend/src/error.rs:121-132 (CompilationError::CodegenFailed
  Display — the `{module}/{symbol}` composition and the nested category prefix);
  repl/spec.md §5.1 (location MUST) and §5.5 (new — compiler-stage subject naming);
  design/arch/fixmes/0907-*.md (the live specimen, a different defect)
status: open
retargeted_by: /design (backend)
retargeted_at: 2026-07-26
ruled_at: design/backend/non-concrete-release-contract.md §3.4 (R-4), §5.5
---

# A codegen-stage failure is presented with a `0..0` span, a doubled category prefix, and a doubled/mangled internal subject

> **RULED S119 Phase 3, `/design`(backend) —
> `design/backend/non-concrete-release-contract.md` §3.4 / §5.5.** Promoted from
> an adjacent experience rider into **rule R-4 of the release contract itself**.
>
> The reason is structural, not courtesy: "a **located refusal the user can act
> on**" is one of the four dispositions the contract assigns, and this FIXME is
> the measurement that today's refusals do not meet that bar. A refusal reported
> at span `0..0` against a `$`-mangled internal instance name
> (`user/user/then$primitives/IO$Int+primitives/IO$Int`) is not a located
> refusal; it is a leak of the compiler's call structure, and it does **not
> discharge the contract**.
>
> Backend-side obligations named at ruling §5.5 (`error.rs:121-132`): one
> category prefix per diagnostic; a real span — `drop_glue.rs:539-544`'s
> `ErrorLocation::from_span(Span::SYNTHETIC)` is the direct cause of `0..0` and
> every registry error should carry the requesting frame's span; and a subject
> the user can look up, with the instantiation rendered as types rather than a
> `$`-mangle. `repl/spec.md` §5.5 remains `/repl`'s normative surface.
>
> Added to the contract's `/review` reject list (§8 item 7): once §5.5 lands, a
> refusal at span `0..0` against a mangled subject is a reject.

## Severity

Important as an experience defect; the underlying compilation failure is a
separate matter with its own owner. This is about the **frame** every
codegen-stage diagnostic is rendered in, so it outlives any one failure: when
FIXME 0907 (the specimen below) is ruled, the next codegen refusal in a
monomorphised instance renders identically.

## What the user sees

Verified at HEAD `4ed43430` at the prompt. Three shapes, one frame:

```
> (match (Pure 5) [(Pure x) x (Effect e) 0])
Error: codegen error at 0..0: codegen failed for user/__expr: codegen error at 0..0: constructor 'Bind' disagrees on declared parameter identity for 'primitives/IO'

> (defn f [] (let [x (Pure 5)] 1))
Error: codegen error at 0..0: codegen failed for user/f: codegen error at 0..0: constructor 'Bind' disagrees on declared parameter identity for 'primitives/IO'

> (defn then [a b] (bind a (fn [_] b)))
:(Fn [(primitives/IO a) (primitives/IO b)] (primitives/IO b)) user/then ; defn
> (then (Pure 1) (Pure 2))
Error: codegen error at 0..0: codegen failed for user/user/then$primitives/IO$Int+primitives/IO$Int: codegen error at 0..0: constructor 'Bind' disagrees on declared parameter identity for 'primitives/IO'
```

## Four distinct defects in that frame

1. **`0..0` — no location.** `repl/spec.md` §5.1 makes the source location a
   MUST. A degenerate span satisfies the letter and none of the purpose: it
   points at nothing. The user typed a 40-character expression and nothing in
   the diagnostic indicates which part, or on a multi-form line which form.

2. **The category-and-span prefix is emitted twice.** `codegen error at 0..0:`
   appears at both the outer and inner wrapper. Nested stage wrapping is being
   surfaced verbatim; the user sees the compiler's call structure.

3. **`user/user/then$primitives/IO$Int+primitives/IO$Int`.** Two problems in
   one token. The `user/user/` doubling comes from
   `error.rs:128` composing `"codegen failed for {}/{}"` over a `Symbol` that
   **already carries its module path** for a monomorphised instance — so any
   codegen failure inside any monomorphised instance renders doubled,
   independent of 0907. And the `$`-mangled instance name is an internal
   monomorphisation artifact; the user defined `then`, and `then` is the subject
   they can act on. (Contrast the middle case, `user/f`, which composes
   correctly — the doubling is specific to the already-qualified instance
   symbol, which is why it survives 0907's ruling.)

4. **`user/__expr`.** An internal synthetic name for "the expression you just
   typed". The subject of a REPL expression is the expression.

## The self-documenting violation, which is the sharpest part

The diagnostic's central noun is undiscoverable at the prompt. Both nouns are:

```
> Bind
Error: type error at 0..4: undefined variable: Bind
> /info Bind
error: unknown symbol 'Bind'
> /info IO
error: unknown symbol 'IO'
```

The user is told a constructor named `Bind` disagrees about `primitives/IO`, and
the REPL then denies that either name exists. The one investigative move
available at the prompt fails on both nouns. (`Pure` *is* discoverable —
`:(Fn [a] (primitives/IO a)) primitives/IO.Pure ; deftype` — so the surface is
inconsistent about the same type's own constructors, which is worse than
uniformly opaque.) Root `CLAUDE.md`'s self-documenting-REPL principle: "No valid
language construct should produce an opaque error."

The `Bind`/`IO` half of this is 0907-specific (they are seeded manually by
`src/bootstrap.rs`, which is why `Pure` introspects and `Bind` does not) and is
recorded there as REPL-experience evidence rather than duplicated here. Items
1–4 above are the frame and are **not** 0907-specific.

## Requirement

`repl/spec.md` §5.5 (new this sprint) states the contract: located at the user's
form; subject named as the user would write it (no `__expr`, no `$` instance
mangle, no doubled module prefix); every noun discoverable or else rephrased;
one located category prefix per diagnostic.

## Why this is filed to `/qa` for attribution rather than to an owner

The message text is composed in `cranelisp-backend`
(`CompilationError::CodegenFailed`'s `Display`, `error.rs:121-132`), but the
inputs come from elsewhere: the `Symbol`'s already-qualified content and the
`__expr` naming are int's, the `ErrorLocation`/span population is a
backend-and-int question (Decision 39 puts coordinates in the variant as data
and formatting downstream in int, so a `0..0` may be an unpopulated location or
a discarded one), and the nested double-prefix is a wrapping decision at the
boundary. That is three candidate homes for four items, and `/repl` is a
black-box viewer with no basis for splitting them.

Per root `CLAUDE.md` §"Usability Findings and Defects", the repro is supplied
above and is one line (`(match (Pure 5) [(Pure x) x (Effect e) 0])`) — but note
it currently rides 0907's refusal, so a guard written against it flips when 0907
lands. `/qa` will want a codegen refusal with an **independent** trigger for the
durable frame guard, or to sequence this behind 0907.

## `/qa` attribution (S118 P6 close, read at source) — SPLIT: backend frame composition + an int presentation rider; S119

Full record: `tests/plan/s118-test-plan.md` §11.8.4. Source read:
`crates/cranelisp-backend/src/error.rs:60-146`,
`crates/cranelisp-types/src/error.rs:192`.

- **Backend (items 1–3, the load-bearing half; this FIXME's new target):**
  - *Doubled prefix* — `CompilationError::CodegenFailed` carries a structured
    `ErrorLocation` but its `cause` is a pre-rendered `String` that already
    embeds the inner types-level located prefix
    (`types/error.rs:192` → `"codegen error at {span}: {message}"`). The
    doubling is baked at the wrapping construction; the fix is structure (or
    stripping) at that seam, never downstream re-parsing.
  - *`user/user/…`* — `error.rs:126-132` composes `"{module}/{symbol}"` over
    an instance `Symbol` that already carries its qualified spelling (plain
    `user/f` composes correctly, so this fires for every monomorphised
    instance independent of 0907).
  - *`0..0`* — the raise sites do not thread the failing form's span into the
    `ErrorLocation`; the spans exist on the `MonoExpr` nodes (the span-keyed
    carrier architecture), so population is a backend raise-site obligation —
    with int required not to discard what arrives.
- **Int rider (item 4 + subject presentation), named for `/design`(int) in
  the same S119 window:** `user/__expr` and the `$`-mangled instance spelling
  are display-boundary subject-presentation defects (D39: coordinates as
  data, formatting downstream in int); the subject must render as the user
  would write it per `repl/spec.md` §5.5. The data (instance symbol) is
  correct — int rewrites the presentation, never the carrier.
- **Guard sequencing:** every currently-reachable e2e trigger for this frame
  is 0907's refusal, so a guard authored now dies with 0907's fix. The §5.5
  frame guard is DEFERRED to S119, authored in the 0907/0903 fix window
  against whatever codegen-refusal trigger remains (or one `/testing`
  constructs). `[S119]` PLAN row landed.

## `/design`(int) ruling on the INT RIDER (item 4 + subject presentation) — S119 Phase 3

Recorded normatively at **`design/int/int.md` §9.1**. This section closes the
rider's design question only; the FIXME stays `target: /design (backend)` for
items 1–3 and is backend's to resolve and delete.

**Ruled: int rewrites the SUBJECT at the display boundary; the carrier is never
touched.** Decision 39 applied unchanged. The `Symbol` backend puts in
`CompilationError::CodegenFailed` is *correct data* — it is the compilation unit
that failed, what `/clif`/`/disasm` take, and what a cache or attribution reader
keys on. Only its rendering to a human is wrong. So the fix is not "stop naming
the instance"; it is one presentation projection.

1. **One subject-presentation function, in `format_error`'s neighbourhood, and
   nowhere else**: `__expr` → the entered form (or a neutral phrase when no form
   text is available); `f$T1+T2` → its base `f`; an already-qualified symbol →
   itself, never re-composed. It is a **projection, not a resolver** — it must
   never look a name up, and must never become a second home for the `$`-mangling
   scheme (the `bare_member_name` precedent, `dotted-ctor-canonical-keys.md`
   §10.4: int reads the projection inverse only).
2. **Applied at `Sess::format_error`, once, for every variant carrying a
   compilation subject** — not at `CompilationError`'s `Display` (backend's, and
   that is items 1–3), not per-command. `int.md` §9 already makes `format_error`
   the single mode-conditional formatter for REPL and batch; a per-site rewrite
   would be the `display-envelope-mirror` class.
3. **Presentation must not erase the investigative handle.** Where the internal
   subject is the only route to the failing artifact, the projection may keep the
   internal spelling in the same diagnostic as a *labelled secondary* — never as
   the headline noun. The self-documenting-REPL requirement is that the central
   noun be actionable at the prompt: `then` is, `user/then$…` is not.

**Guard sequencing accepted as `/qa` set it**: int's rider rides the deferred
§5.5 frame guard authored in the 0907/0903 fix window against whatever
codegen-refusal trigger remains. Int does **not** get a private guard keyed on
0907's message text. The `Bind`/`IO` undiscoverability half stays 0907's.

## Note on the S117 fix this does not contradict

S117 fixed the failed-codegen diagnostic to "name the actual failed compilation
subject rather than `/`" (`sprints/archive/`, `design/int/s117-conformance-recovery.md`).
That fix holds — the subject is populated now. This FIXME is about the *form* of
the populated subject, not its absence.
