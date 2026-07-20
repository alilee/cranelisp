# Qualified binder-head rejection — the W3 binder-family seam (S113)

> Subordinate topic doc, cited from `design/frontend/frontend.md` §4.2. Owned by
> `/design` (frontend). Authored S113 Phase 3 for SPRINT.md §Scope-C, against the
> `/arch` Phase-2 architecture-review ruling **Q3** (SPRINT.md §"Architecture
> review" Q3). Pre-implementation; `/dev`(frontend) implements in W3, `/review`
> checks against it.

Spec anchor: `spec/05-definitions.md` §5 intro — **"Declaration heads are
binders"** (user ruling 2026-07-18, generalized to every binder head; veto
window closed S112 Phase 7). A declaration head is a **binder, not a
reference**, and MUST be a **bare (unqualified) symbol**; a qualified spelling
in head position is a **compile-time error** (the dual of the §8.5 reference
rules). Test contract: `tests/plan/s113-test-plan.md` §1.2 (BD-M1..M5).

---

## 1. The problem — 3+ silent-accept faces the reject closes

Today the head-parse sites accept a qualified head and re-root it under the
current module (the D-qual class, `crates/cranelisp-frontend/CLAUDE.md`
§Qualified-name splitting). The S112 rulings-rider probes pinned three RED faces
(archive/sprint-112.md §Outcome; suite REDs, `class=silent-accept owner=/dev`):

| Written form | Live face today (both wrong) |
|---|---|
| `(defn fmt/foo [x] x)` | REPL **silently binds** `user/fmt/foo` + echoes `; defn`; under `--run` the defn accepts and the failure is deferred to the reference site as an incidental `module 'fmt' … not found` (a **mode-divergent** face) |
| `(deftrait fmt/Foo …)` | WITH a matching module present → silently binds `user/fmt/Foo` (`; deftrait` echo); WITHOUT one → dies with an incidental `module 'fmt' … not found` at a degenerate `0..0` span |
| `(deftrait (fmt/Foo f) …)` | same dual face on the parenthesized head |

Both faces violate the binder principle: a binder introduces a name **where it
is written**, so it carries no module qualifier and there is no mechanism for
declaring a name into another module. The reject converts each into a single,
**located**, parse-time diagnostic that names the fix.

## 2. The seam — ONE shared `reject_qualified_binder_head` (Principle 7)

Fix shape per `/arch` Q3: **one** shared primitive beside the existing
`reject_reserved_binder_name` (`ast_builder.rs:75`), applied at every binder
head site — **never per-form copies**. The two rejects are siblings: one gates
reserved names (`trace`), one gates qualified spellings; both are single-sourced
so every head site enforces the identical rule (Principle 7, Principle 18 —
enforce the invariant where binder-ness is decided).

```
/// Reject a qualified (slash-bearing) spelling in DECLARATION-HEAD position.
/// A declaration head is a binder, not a reference (spec §5, "Declaration heads
/// are binders") — it binds a NEW name into the CURRENT module and MUST be a
/// bare (unqualified) symbol. A qualified head (`fmt/foo`, `fmt/Foo`) is a
/// compile-time error; there is no mechanism for declaring a name into another
/// module. Single-sourced (Principle 7) so every binder head site enforces the
/// identical rule.
pub(crate) fn reject_qualified_binder_head(name: &str, span: Span)
    -> Result<(), CranelispError>
```

**Predicate (settled — as landed W3).** A name is qualified **iff splitting at
the LAST `/` yields two NON-EMPTY halves** — `name.rsplit_once('/')` with
`!module.is_empty() && !bare.is_empty()` (`ast_builder.rs:111`
`reject_qualified_binder_head`). This is the **exact** guard the §8.5 reference
splitters use (`type_ref_from_name`/`trait_ref_from_name`,
`ast_builder.rs:1726/1742`), so the reject is their precise **dual**: a reference
splits `module/Name` and reaches across modules; a declaration head is a binder
and stays bare.

> **The both-halves-non-empty condition is load-bearing (Principle 16) — the
> bare `/` operator cell.** A naive `name.contains('/')` was **falsified in W3
> implementation** (FIXME 0659): it rejects the legitimate bare `/`
> division-operator binder — `Num` declares a method **named `/`**
> (`(deftrait Num … (/ [a b] self))`, `stdlib/num/num.cl`), and `"/".contains('/')`
> is `true`, so the coarse predicate reds ~40 stdlib e2e tests (`undefined
> variable: +`, the whole prelude fails to compile). `/`, `foo/`, `/bar` all
> split to an empty half and are therefore **NOT** qualified — exactly as the
> reader keeps a bare `/` a bare operator name (its own `/`-split guard "requires
> BOTH halves non-empty"). The design's own §8.5-dual framing was always correct;
> only the one-line "Predicate" shorthand was wrong, and the landed code
> implements the split, not the `contains`. Unit-pinned:
> `ast_builder/tests.rs::reject_qualified_binder_head_rejects_slash_and_names_bare_fix`
> + `deftrait_slash_operator_method_name_accepts`.

> **`.` (dotted-member) note.** The predicate keys on `/` only. A dotted name
> (`Point.x`) is a member/accessor form, not a module qualifier, and never
> appears in a raw declaration-head slot (the generated `Type.field` accessor is
> synthesized, not user-written as a `defn` head). Widening the predicate to `.`
> is out of scope (Principle 6 — no speculative widening); if a future dotted
> head cell appears it is a `/qa` matrix row, not a helper change.

### 2.1 Diagnostic shape (self-documenting REPL principle)

Consistent with the S112 deftrait/impl-head reject diagnostics
(`trait-impl-head-parse.md` §4 — `parse_err` with the **span of the offending
head**, `Sexp::format_flat()` never `{:?}`, each names the fix). The message:

```
'{name}' is a qualified name, but a definition head is a binder and must be a
bare (unqualified) name — write '{bare}' (a definition binds into the current
module; use an import/qualified reference to reach another module)
```

where `{bare} = name.rsplit('/').next()` (the after-last-slash segment — the
name the user most likely meant to bind). This is fix-naming (§5-binder
principle) and matches the located-reject shape the RED pins assert
(`assert_err_span_at` / span-points-at-head, BD-M1).

## 3. The head sites — exhaustive enumeration

Every site is a `pub(crate)`/private head-parse point already in the crate; the
reject is a **one-line insertion** at each, mirroring how `reject_reserved_binder_name`
is threaded (`ast_builder.rs:500/1446/1634/1653/1840/1845`, `defmacro.rs:135…`).

| # | Site | `ast_builder.rs` / `defmacro.rs` | Spec §5 native form(s) | Head shape |
|---|---|---|---|---|
| S1 | `get_defn_name` | `ast_builder.rs:497` | `defn`/`defn-` **AND** impl-body method defns | bare `Symbol` |
| S2 | `build_type_head` | `ast_builder.rs:597` | `deftype`/`deftype-` | bare `Symbol` OR `(Name params…)` head[0] |
| S3 | `parse_trait_head_shape` | `ast_builder.rs:855` | `deftrait`/`deftrait-` | bare `Symbol` OR `(Trait con_var)` head[0] |
| S4 | `parse_defmacro` name | `defmacro.rs:239` | `defmacro`/`defmacro-` | bare `Symbol` |
| S5 | `build_method_sig` name | `ast_builder.rs:957` | deftrait method-signature name | bare `Symbol` (`children[0]`) |

**S5 is beyond arch Q3's explicit seam list — required by BD-M1 + spec §5.3.3;
see §8 for the spec-diff finding.** A deftrait method signature introduces its
method name into scope (`spec/05 §5.3.3` — "A trait declaration introduces method
names into scope"), so a qualified method name `(deftrait Foo (fmt/show [x] Int))`
is a qualified binder. `tests/plan/s113-test-plan.md` BD-M1 pins "deftrait
METHOD-name position", but arch Q3's seam list and spec §5's *explicit
native-binder-head enumeration* both omit it (they name only the def-form heads +
impl-body method defns). Insert at `build_method_sig:957` (`expect_symbol`
already yields the span — currently discarded as `_`; capture it for the located
reject). §8 routes the spec-enumeration gap to /spec.

**S1 covers TWO spec cases through ONE seam.** `get_defn_name` is called both by
`parse_defn` (`:451`) and by `build_impl_method` (`:1202`) — so the impl-body
method-defn head (`spec/05 §5` intro: "the method definitions inside an `impl`
body … Each of their heads is a binder") is covered for free by inserting the
reject once in `get_defn_name`. No separate impl-method site. (Impl **slot-1**
echoes a trait *reference*, not a binder — `spec/05 §5` parenthetical, and it
already routes through the D-qual splitter `trait_ref_from_name`, so it is
correctly NOT a reject site.)

**S2/S3 insertion point.** For the parenthesized heads the reject applies to the
**head-name element** only — `children[0]` after it is confirmed to be an
uppercase `Sexp::Symbol` (the existing dispatch-order-is-head-before-arity rule,
`trait-impl-head-parse.md` §4). Insert after the uppercase check, before
`TypeName::from` / `TraitName::from` (which today swallow the whole slash-name
into the current module — the D-qual re-root the reject pre-empts).

- S2 `build_type_head`: reject in **both** arms — the bare `Symbol` arm
  (`:599`) and the `(Name params…)` list arm on `children[0]` (`:606`).
- S3 `parse_trait_head_shape`: reject in **both** arms — the bare `Symbol` arm
  (`:859`) and the `(Trait con_var)` list arm on the head name (`:875`). Because
  `parse_trait_head_shape` is the ONE shared shape parser for `deftrait` AND
  `impl` slot-1, inserting here would also reject a qualified `impl` slot-1 head
  — **but** `impl` slot-1 is a trait *reference* (qualified is legal, D-qual
  splits it). So the reject must **not** live inside the shared shape parser;
  it lives in `build_trait_head` (`:935`, the deftrait-specific caller that owns
  the binder policy), NOT in `parse_trait_head_shape`. This preserves the §3
  "name policy stays caller-side" split of `trait-impl-head-parse.md` — the
  shared parser stays shape-only; the binder reject is a deftrait-caller policy,
  exactly as `TraitName::from` (home-module, no split) already is.

### 3.1 The con_var sibling cell (BD-M4 / S112-F3 residual)

`spec/05 §5.3.2` grammar: `con_var = lowercase_symbol` (a **bare** lowercase
identifier). `parse_trait_head_shape` already rejects an **uppercase** con_var
(`:907`), but the case check keys on the after-slash segment (`is_uppercase_start`,
`:120`), so a **slash-bearing** con_var `(deftrait (Functor prim/x) …)` passes
the lowercase gate today — the known-open F3 residual
(`trait-impl-head-parse.md` §4 F3 note; `tests/plan/s113-test-plan.md` BD-M4).
A qualified con_var is a qualified **binder** (it binds a type-constructor
variable into the trait's scope) → the SAME family. **Fold it into W3**: apply
`reject_qualified_binder_head` to the con_var symbol at `parse_trait_head_shape:898`
(the con_var arm), located at the con_var span, naming the bare-lowercase rule.
This is inside the shared shape parser (con_var is a binder in **both** deftrait
and impl echoed-head — `(impl (Functor prim/x) …)` is equally malformed), so
unlike the trait-name reject it correctly lives in `parse_trait_head_shape`.

### 3.2 Type-parameter symmetry (flagged, not a W3 blocker)

`build_type_head`'s `(Name params…)` arm binds each `param` as a type variable
(`:607`). A qualified type param `(deftype (Pair prim/a b) …)` is the same
qualified-lowercase-binder shape and currently accepts (`expect_symbol` only).
Spec §5's principle names the **head name** specifically, not the secondary
type-param binders, so this is **not** in the S113 reject scope; it is a
symmetry candidate for `/qa`'s matrix (a `/qa` row, mirroring how F3 con_var was
routed). Named here so the enumeration is complete and the exclusion is
deliberate; `/dev` does not action it in W3 unless `/qa` adds the row.

### 3.3 deftype variant-constructor / field / platform names — LANDED (FIXME 0660 closed)

`/review` (S113 W3) found that **deftype variant-constructor names are binders
missed on all three sides** — spec §5's enumeration, this design's §3/§8, and
/qa's BD-M1 matrix. A variant ctor "introduces a distinct variant" (spec §5.2.2)
and mints a module-level callable — the exact analogue of the S5 method-signature
name (§5.3.3) the design DID include. The user RULED 2026-07-19 that
variant-constructor and field names ARE binders ("you can't define a name in
another module, only reference"); /spec scribed §5 intro + the §5.2.2/§5.2.6
per-site bullets + §5.10 platform simple-symbol clause `[S113]`. **All three
cells' implementation LANDED in the same wave** (verified in source S114 Phase 3):

**(a) ctor-name uppercase gate on the list arm — LANDED.** The data-ctor list
arm now checks `is_uppercase_start` (`build_constructor_def`
`ast_builder.rs:719`), rejecting `(deftype Shape (circle [:Int r]))` located at
the name with a fix-naming message (write `Circle` — matchable in patterns). This
was the exact mirror of the `build_type_head` list-arm case defect the same wave
fixed (audit S113 finding 2) — a settled defect class, no user ruling needed.

**(b) ctor-name qualified reject — LANDED (settled by the 2026-07-19 ruling).**
`reject_qualified_binder_head` now fires in **both** arms —
`ast_builder.rs:694` (bare-nullary) and `:712` (list, checked BEFORE the
uppercase rule so a qualified name reports the qualified fault regardless of its
after-slash case). `(deftype Shape (fmt/Circle …))` rejects located at the ctor
name instead of accepting and dying at the degenerate `0..0` span.

**(c) field names + `platform` name — LANDED.** Field names carry
`reject_qualified_binder_head` in both arms of `build_field_list`
(`ast_builder.rs:793` annotated, `:804` bare) — a field binder mints a
`Type.field` accessor (§5.2.6), so a qualified spelling `(deftype P [:Int fmt/r])`
rejects located at the field name. The `platform` name adopts the **`mod`-model**
module-phase guard (`parse_platform` `module_extract.rs:455` —
`name.contains('/') || name.contains('.')`, NOT `reject_qualified_binder_head`
which is `/`-only), symmetric with `parse_mod_decl:181`; a qualified/dotted
platform name would corrupt the composed `platform.<name>` module path. Field
names are NOT a §3.2-style justified exclusion after all — the user's ruling
made them binders, and the accessor-minting seam is a clean name-based reject
site, so they landed with the ctor cells rather than deferring to a /qa row.

**Type-params remain the one justified exclusion** (§3.2) — spec §5's principle
names the head name + the now-scribed ctor/field/method-sig binders, not the
secondary type-param binders (`(deftype (Pair prim/a b) …)`); that stays a /qa
matrix candidate. `/qa`'s BD-ctor matrix rows (qualified-reject, lowercase-list-arm
twin, bare-uppercase twin) are tracked in `tests/plan/s114-test-plan.md` §5.3
(reserved rows against this now-final enumeration). **FIXME 0660 is deleted** —
spec (done /spec), design enumeration (this §3.3 + §8), and implementation (all
three cells) are complete; the /qa rows are the plan's to draw.

### 3.4 Value-level local binders — the re-landing (0670-gated, F8 wave 2)

The §5 native-head reject covers **declaration heads**. Spec §5's binder-position
table also names the **value-level local binders** — `defn`/`fn`/`defmacro`
params, `let` names, `match` var-patterns — as bare-symbol binders. Their reject
was **deferred** at S113 (crate `CLAUDE.md` §"DEFERRED — value-level local
binders"; the three NOTE comments at `build_annotated_params:2001`,
`build_let_bindings:1588`, `build_pattern:1780`): these `build_form` seams run
AFTER int's macro-expansion name-resolution, which itself **qualifies** a local
binder whose name collides with an importable symbol (`name` →
`primitives/name`, only when a macro is in scope), so a build-layer reject fired
on int's mangled output and broke the VALID program `(defn f [name] (str … name))`.

**0670 unblocks this (ruled path 1, /arch Phase 3):** int's expansion-pass
qualification now **skips binder slots** — a binder is never a reference, so it
is never a candidate for name-resolution. The int fix is Track C (src-surface,
F8 wave 1); the mandatory expansion-seam unit test (a colliding param stays
**bare** through expansion) is /dev(src)'s. Once it lands, a raw qualified binder
name reaches these seams unmangled, so `reject_qualified_binder_head` is sound at
each:

- **`build_annotated_params`** (`ast_builder.rs:1972`) — insert after each
  `reject_reserved_binder_name`, in BOTH the annotated arm (`:2000`) and the bare
  arm (`:2013`). Covers `defn`/`defn-` params, `fn` params (via `build_fn`), and
  `defmacro` params (via the same builder) — one seam, three forms.
- **`build_let_bindings`** (`:1580`) — insert after `reject_reserved_binder_name`
  (`:1587`).
- **`build_pattern`** (`:1766`) — insert at the lowercase var-binder arm
  (after `:1784`) AND on each constructor-pattern **binding** symbol
  (`:1806-1807`). NOT on `children[0]` (the ctor name is a REFERENCE, spec
  §6.2.1 — a qualified ctor pattern head is legal and splits).

The SAME `reject_qualified_binder_head` helper (`:111`, both-halves-non-empty
predicate, Principle 16) — no per-seam copy (Principle 7). This makes the
value-level cells (IQ-N1..N4, `s114-test-plan.md` §4.3) reject located at the
user's written form, with the bare-colliding-binder twin (`(defn f [name] …)`)
staying LEGAL (the reject fires on the qualified spelling, not on the collision).

**`/dev`(frontend) retirements riding this wave** (crate `CLAUDE.md` +
source — `/dev`-owned, named here for the wave brief): the three NOTE comments;
the §"DEFERRED — value-level local binders" section; and the **degenerate-`foo/`
mirror sentence** (crate `CLAUDE.md`:114 + `ast_builder.rs:2082-2086`
`type_expr_to_trait_ref` debug_assert comment) — superseded by 0684 (bare `foo/`
now rejects at the reader, `enforcement-matrices.md` §3.2, so only bare `/`
division reaches the splitters unsplit).

**Sequencing (F8 strict order):** 0670 int fix (Track C) → this re-landing
(Track D) → /testing IQ-N1..N4 cells (Track D wave 3). This is the ONLY Track-D
frontend item gated on 0670; §3.1–§3.3 (binder heads, con_var, deftype-ctor
family) and `enforcement-matrices.md` (BD-A, RA) are all independent.

## 4. Span provenance across macro expansion — the LOAD-BEARING finding

`spec/05 §5` (intro + §5.6 + §5.7) and `tests/plan/s113-test-plan.md` BD-M2/M3
carry a hard MUST for the macro-route binders (`def`/`def-`, `const`/`const-`,
and any **user** inline `defmacro` whose expansion emits a qualified binder
head):

> the rejection fires on the **expanded** `defn`/`defmacro`, but the diagnostic
> span MUST point at the **user's written form** — the `def`/`const` head as
> typed — **not** the synthesized expansion.

**Finding: the frontend seam CANNOT satisfy this MUST alone. The int
macro-expansion pipeline discards all source provenance from macro output.**
Two mechanisms destroy it, verified on HEAD:

1. `src/marshal.rs:62` — "All output spans are `Span::SYNTHETIC`": every Sexp a
   macro returns is unmarshalled with `Span::SYNTHETIC` (`:83–100`).
2. `src/expander.rs:158` `execute_matched_clause` → `rewrite_spans(&mut result, span)`
   → `rewrite_spans_unique` (`:679`), which **ignores** the call-site `span` it
   is handed (`_call_site_span`, `:674`) and assigns a **fresh unique synthetic
   span** (`next_synthetic_span()`) to **every** node.

So for `(def fmt/x 1)` — which expands to
`(begin (defn fmt/x-def [] 1) (defmacro fmt/x [] …))` (`stdlib/defs.cl:24`) —
the synthesized `defn` head `fmt/x-def` and `defmacro` head `fmt/x` both carry a
synthetic span (≥ 1_000_000, mapped to no source byte). The reject **fires
correctly** (both heads contain `/`), so **correctness is preserved** — the
qualified macro-route head IS rejected — but on TWO axes the diagnostic
**degrades**:

- **span**: points at a synthetic offset, not the user's `(def fmt/x 1)` form —
  the same degenerate-location failure the deftrait pins already complain about;
- **shown name**: for `def` (which mangles `~impl-name = fmt/x-def`), the
  FIRST-processed head is the synthesized `fmt/x-def`, so the message would name
  the mangled synthesized head, not the written `fmt/x`. (`const` is cleaner —
  its `defmacro` head is `~name = fmt/x` verbatim, no mangle — but the span is
  still synthetic.)

**Native forms are unaffected and fully satisfy the MUST.** A directly-written
`(defn fmt/foo …)`/`(deftype …)`/`(deftrait …)`/`(defmacro …)` is a special
form, not a macro; its head is never marshalled and int's `expand_scoped`
preserves child spans (`expand_children_clone`), so the head carries its **real
reader span** → located reject, correct name. The gap is **exclusively** the
macro-route (BD-M2/M3), and it is an **int-surface** gap, not a frontend one.

### 4.1 Why the deep fix is wrong, and the recommended paired seam

**Rejected — preserve spans through the marshal boundary.** Giving macro-output
nodes their original source spans collides head-on with the span-**uniqueness**
invariant that `rewrite_spans_unique` exists to maintain: the span-keyed
carriers of `design/arch/backend-keyed-consumer.md` (`resolved_targets`
sidecar) require every node in a minted/expanded body to have a **unique** span,
or span-keys collide. A macro-output node cannot carry BOTH a source-anchored
span (for diagnostics) AND a unique synthetic span (for carriers) in one `Span`
field. HIGH blast radius, breaks a landed arch invariant — rejected.

**Rejected — a pre-expansion special-case for `def`/`const`.** Detecting the
qualified head on the raw `(def …)`/`(const …)` form before expansion would be a
SECOND binder-reject seam that knows specific stdlib macro names — violating
Principle 19 (no module privileged by name) and re-opening the per-form drift
the shared helper exists to close. Rejected.

**Recommended — a paired int-side re-anchoring seam (mirror of the 0613
quote-shield pairing).** The frontend fold + int shield precedent
(`quasiquote-fold.md` §7; two `/dev` surfaces, one logical wave) is the template:
frontend lands the reject (this doc); int lands a small **error-relocation** at
the expansion→build boundary. int already knows the original form's real span
and threads it as `origin_span` for diagnostics raised *during* expansion (FIXME
0485; `src/expander.rs:707` doc, `call_span = origin_span.unwrap_or(span)` at
`:902/:944`). The binder reject fires *after* expansion returns (at `build_form`),
so the mechanism is: **when int drives `build_form`/`build_forms` on
macro-expansion output and it returns a binder-reject `ParseError`, re-anchor
that error's `location` to the original source form's span** (the span int holds
for the pre-expansion form) — and, where feasible, phrase the message in terms
of the written head. This keeps span-uniqueness intact (macro output keeps its
unique synthetic spans for carriers) while giving the diagnostic a real source
location. Cost: a small int-side relocation seam, entirely within the existing
FIXME-0485 origin-span discipline — NOT a macro-span-model rework.

**Sequencing (per the 0613 precedent).** The frontend reject is inert-safe
without the int seam — a qualified macro-route head still rejects (correctness),
only the *location/name* of that one diagnostic degrades to synthetic. So the
frontend reject may land in W3 ahead of the int seam; the int re-anchoring lands
≤ W3/W4 to satisfy the BD-M2/M3 span MUST. This cross-surface obligation is
filed as a FIXME `target: /arch` (the pairing decision touches the
span-uniqueness/carrier invariant that is arch-owned) and surfaced in the SPRINT
§Skill-plan so `/sprint` routes the paired int dispatch.

## 5. 0589 — the sibling annotation-path seam (NOT the binder-head seam)

FIXME 0589 (qualified-lowercase annotation `:user/int` mints a `TypeVar`
carrying a `/`) is the **same family** (a frontend qualified-name lexical-class
decision) but a **different, sibling seam**: it is the **annotation/reference**
path, `parse_annotation_name` (`ast_builder.rs:1750`), NOT a declaration-head
binder. It must **not** be conflated with `reject_qualified_binder_head` — an
annotation `:user/int` is a *reference* position (a qualifier there is
meaningful, it reaches another module), so the fix is not a reject but correct
**routing**.

**Seam answer.** `parse_annotation_name` decides "is this a type var?" by
`is_uppercase_start` (which tests the after-slash segment only), so `user/int`
(lowercase after slash) routes to `TypeVar("user/int")` carrying the slash — the
Principle 18 violation 0589 names ("a `TypeVar` is a bare lowercase identifier;
it must never carry a `/`"). **Fix (W3, one line, infallible — no span
threading, signature unchanged):** a lowercase name that **contains `/`** is not
a valid type var (spec §3.3 — a type var is a bare lowercase identifier), so
route it to `Named` (which splits the module off via `type_ref_from_name`)
rather than `TypeVar`:

```
fn parse_annotation_name(name: &str) -> TypeExpr {
    if name == "self" { TypeExpr::SelfType }
    else if is_uppercase_start(name) || name.contains('/') {
        // qualified-lowercase (`user/int`) is NOT a bare type var (spec §3.3);
        // route through the §8.5 splitter so the unknown-type error names the
        // module — a TypeVar must never carry a `/` (Principle 18, FIXME 0589).
        TypeExpr::Named(type_ref_from_name(name))
    } else {
        TypeExpr::TypeVar(name.into())
    }
}
```

The existing in-crate typecheck backstop (`resolve::resolve_type_expr`'s
`!contains('/')` mint guard, landed S109, `u8_qualified_lowercase_name_does_not_mint`)
**stays** as the structural fence; this frontend leg makes the routing decision
correct **where type-var-ness is decided** (Principle 18), so no downstream
capability inherits the looseness. Both `parse_annotation_name` callsites
(`:1697` param annotation, `:1943` return type) are covered — one function, one
fix.

**Decoupled from 0590.** 0589's earlier note said the frontend leg "folds into
0590's P7 refactor". That is superseded: 0590's four mirror resolvers are all in
`crates/cranelisp-typecheck/` (see §6), a different crate — the frontend routing
leg cannot literally fold into a typecheck refactor. The frontend leg is a
self-contained one-line routing fix that lands in W3 independent of 0590. `/dev`
closes 0589 when this frontend leg + the standing typecheck backstop hold
(program-seam cell `(defn f [:m/x v] v)` errors naming the module).

## 6. 0590 disposition — NOT frontend surface (re-target /design(typecheck))

FIXME 0590 (four parallel `TypeExpr` resolvers each hand-roll mint-on-miss) is
**not** frontend-resolver-shaped. Its `refers_to` and all four named resolvers
live in `crates/cranelisp-typecheck/src/` — `traits/type_resolve.rs`
(`resolve_trait_type_expr`, `resolve_type_expr_hkt`, `resolve_type_expr_hkt_impl`),
`form.rs` (`check_type_expr` + `collect_type_var_ids`), converging onto
`resolve.rs::resolve_type_expr`. `/design` is narrow-deployed per crate; a
frontend deployment owns none of these files. The convergence is a real P7
`resolver-mirror` concern, but it is a **typecheck-crate** design task requiring
a shape for Self-substitution + HKT con-var interception + a ruling on the
`_hkt`/`_hkt_impl` never-error `Named` arms (0590 §"Proposed resolution") — all
typecheck-internal.

**Disposition: re-target to `/design`(typecheck), defer to S114.** It is **not**
in S113's typecheck wave (W2 is mono/carrier-family only — R1/R2/D3/TB-24/D1/D2,
SPRINT §Scope-B); opening a resolver-convergence refactor there would exceed
that wave's scope. Kept **open** (the convergence has not happened) with the
target/schedule updated. The 0590 rustdoc-inaccuracy sub-item (the resolve.rs /
checker.rs rustdoc wrongly names "trait-method sig" as a `mint=None`
still-errors context) is a `/dev`(typecheck) doc fix independent of the
convergence and rides whenever typecheck is next deployed.

## 7. Corpus-sweep consumption (arch seam flag iii / revision 6)

Turning the head sites' silent-accepts into rejects can break fixtures that
accidentally use qualified heads. W1 (`/testing`) produces the qualified-head
corpus sweep across `tests/` (incl. `tests/fixtures/`), `examples/`,
`repl/demos/` (+ archive), `exemplar/` — native AND macro-route
(`tests/plan/s113-test-plan.md` §1.3; **W3 does not open until that table
exists**). Seed evidence (/qa grep) says the corpus is **likely clean** (the
single-line pattern hits only the deliberate binder pins). W3's landing
discipline:

- **W3 ships rejects + fixture fixes in ONE change-set** (atomic). If the sweep
  table lists any qualified-head fixture, the reject and its fix land together —
  never a reject that reds a fixture in a separate commit.
- The reject is **error-path only** — zero `public-api.txt` diff (arch §Public-API
  discipline: "binder work is error-path-only"). `/dev` confirms the baseline is
  unchanged at PR time.
- Examples/repl/exemplar gates stay green in the same change-set (BD-X2).

## 8. Spec-diff — §5 binder cases vs this design's sites (the S113 process rule)

Per SPRINT §Scope-F ("diff the design's case list against the spec's before
Phase-3 exit") and `tests/CLAUDE.md` §"Coverage by definition variants". Spec §5
enumerates the binder heads; this design's sites are checked against them:

| Spec §5 binder case | Reference | This design's site | Covered? |
|---|---|---|---|
| `defn`/`defn-` head | §5, §5.1.1 | S1 `get_defn_name` | ✓ |
| impl-body method-defn head | §5 intro ("method definitions inside an `impl` body") | S1 `get_defn_name` (shared caller) | ✓ (same seam) |
| `deftype`/`deftype-` head | §5, §5.2:171 | S2 `build_type_head` (both arms) | ✓ |
| `deftrait`/`deftrait-` head | §5, §5.3:322 | S3 `build_trait_head` (both arms) | ✓ |
| `defmacro`/`defmacro-` head | §5, §5.5:474 | S4 `parse_defmacro` name | ✓ |
| deftrait method-signature name | §5, §5.3.3 (introduces method names into scope) | S5 `build_method_sig` | ✓ (BD-M1) — **spec enumeration LANDED** (§5 intro + §5.3.3 `[S113]`, /spec scribed post-Phase-3) |
| `def`/`def-` head (macro route) | §5, §5.7:544 | S1 post-expansion + §4 span seam | ✓ correctness; span → int seam (§4) |
| `const`/`const-` head (macro route) | §5, §5.6:522 | S4 post-expansion + §4 span seam | ✓ correctness; span → int seam (§4) |
| con_var (secondary binder) | §5.3.2 grammar | §3.1 `parse_trait_head_shape` con_var arm | ✓ (BD-M4, folded) |
| **deftype variant-ctor name — uppercase gate** (list arm) | §5.2.2 (introduces a distinct variant) | §3.3(a) `build_constructor_def:719` list arm | ✓ **LANDED** — mirror of the fixed `build_type_head` list arm |
| **deftype variant-ctor name — qualified reject** | §5.2.2 | §3.3(b) `build_constructor_def:694/:712` both arms | ✓ **LANDED** — settled by the 2026-07-19 ruling (variant-ctor names are binders) |
| deftype field names (secondary binder) | §5.2.6 | §3.3(c) `build_field_list:793/:804` both arms | ✓ **LANDED** — ruled a binder (mints `Type.field` accessor); qualified rejects |
| `platform` name | §5.10 | §3.3(c) `parse_platform:455` | ✓ **LANDED** — `mod`-model `/`+`.` guard (module-phase, not `reject_qualified_binder_head`) |
| deftype type-params (secondary binder) | §5.2 grammar | §3.2 | flagged to /qa, **justified exclusion** (spec §5 principle names the head name, not secondary param binders) |
| `mod`/`mod-` name | §5.8 | — | **justified exclusion**: `mod` already requires "a simple symbol (not qualified, not dotted)" (§5.8) — enforced at `module_extract.rs`, a module-phase decl, not a §5 declaration-head binder; not a new S113 site |

**Result: the diff is NON-EMPTY on one axis, with the delta justified and
routed.** For the def-form heads + both macro-route forms + impl-body method
defns, the design's sites match spec §5's explicit enumeration exactly (empty
diff). The **one delta**: the **deftrait method-signature name** (S5) is a binder
by §5.3.3 ("introduces method names into scope") and is pinned by /qa's BD-M1
matrix, but it is **absent from spec §5's explicit native-binder-head
enumeration** (which lists only the def-form heads + impl-body method defns) AND
from arch Q3's seam list. The design **includes** the site (a qualified method
name is nonsensical — you cannot declare a method into another module — and
`build_method_sig` is a clean, name-based seam the shared helper covers
uniformly), and the spec-enumeration gap was routed to /spec and **LANDED**: §5's
intro paragraph now enumerates "the method-signature names inside a `deftrait`"
alongside the impl-body method defns, and §5.3.3 carries the per-site binder note
(both `[S113]`, /spec scribed post-Phase-3). Spec head enumeration and the
implementation's site set are now two-sided-complete for the method-name axis.
(The originating FIXME 0651 was actioned and deleted.)

**Second delta family (was FIXME 0660, /review-found post-Phase-3): the deftype
variant-constructor cells — now CLOSED.** The enumeration originally missed
variant-ctor names on all three sides (spec §5, this diff, /qa's BD matrix). The
user ruled 2026-07-19 that variant-ctor AND field names are binders; /spec
scribed §5 intro + §5.2.2/§5.2.6/§5.10 `[S113]`; and all four implementation
cells LANDED (§3.3): **(a)** the list-arm uppercase gate, **(b)** the ctor-name
qualified reject (both arms), **(c)** field-name qualified rejects (both arms) +
the `platform` `mod`-model `/`+`.` guard. The remaining deltas (type-params,
`mod`) stay justified-excluded with rationale; con_var and the deftype-ctor
family are dispositioned. No design site lacks a spec basis; every §5-family
binder cell is now **covered or justified-excluded**. FIXME 0660 deleted; the
/qa BD-ctor matrix rows are reserved against this final enumeration
(`s114-test-plan.md` §5.3).

## 9. Testability (Principle 5)

Every site is a pure `&Sexp`/`&str` → value function, unit-testable with no
session (the crate-wide property, `frontend/CLAUDE.md` §Debugging). Unit tier
(`ast_builder/tests.rs`, `defmacro/tests.rs`), asserting the located reject:

- per native head site (S1–S5): a qualified head → located `parse_err` (span
  points at the head, message names the bare fix) + a bare-head **positive
  twin** that still parses (BD-M1's one-reject-plus-one-bare-twin-per-form);
- con_var (§3.1): `(deftrait (Functor prim/x) …)` and `(impl (Functor prim/x) …)`
  both reject at the con_var span (BD-M4);
- the S1-shared-seam property: a qualified head rejects **identically** whether
  reached via `parse_defn` or `build_impl_method` (the Principle-7 single-source
  guard — the instrument that proves no impl-method copy grew).

E2e/matrix (BD-M1..M5 + the macro-route span provenance BD-M2/M3) is
`/qa`+`/testing`-owned; the frontend unit tier pins the boundary. The
span-provenance BD-M2/M3 e2e is the durable proof of the §4 int-seam obligation
— it fails (degenerate span) until the paired int re-anchoring lands, so it is
the trigger that keeps the int seam honest.

## 10. Principles cited

- **Principle 7 (single source of truth)** — ONE `reject_qualified_binder_head`
  at every head site; no per-form copies (§2); the shared-parser-vs-caller-policy
  split preserved (§3, trait-name reject in `build_trait_head`, con_var reject
  in `parse_trait_head_shape`).
- **Principle 18 (enforce invariants structurally)** — the reject fires where
  binder-ness is decided; 0589's routing decision made correct at the
  type-var-ness decision point (§5), never merely backstopped downstream.
- **Principle 19 (no module privileged by name)** — the macro-route span fix is
  NOT a `def`/`const`-name special-case (§4.1).
- **Principle 6 (complexity has a budget)** — predicate keys on `/` only, no
  speculative `.` widening (§2 note); type-param symmetry deferred not built (§3.2).

## 11. Cross-references

- `design/frontend/frontend.md` §4.2 — this doc named in the master.
- `design/frontend/trait-impl-head-parse.md` §3/§4 — the shared-shape-parser vs
  caller-name-policy split the trait-name reject placement honors; the F3 con_var
  residual this doc folds in.
- `design/frontend/quasiquote-fold.md` §7 — the frontend+int paired-seam
  precedent the §4 span-re-anchoring mirrors.
- `design/arch/backend-keyed-consumer.md` §1.1 — the span-uniqueness/carrier
  invariant that forbids the deep span-preservation fix (§4.1).
- `crates/cranelisp-frontend/src/ast_builder.rs` :75 (`reject_reserved_binder_name`),
  :497 (`get_defn_name`), :597 (`build_type_head`), :855/:935
  (`parse_trait_head_shape`/`build_trait_head`), :1750 (`parse_annotation_name`,
  0589); `defmacro.rs` :239 (`parse_defmacro` name).
- `src/marshal.rs:62` + `src/expander.rs:674/158` — the span-provenance loss (§4).
- `tests/plan/s113-test-plan.md` §1.2/§1.3/§4 — BD-M1..M5 + corpus sweep + W3 rows.
- `design/arch/fixmes/0589-*`, `0590-*` — the annotation/resolver legs (§5/§6).
- `design/arch/fixmes/0650-*` — the paired int-side span re-anchoring seam,
  `target: /arch` (§4 finding).
- FIXME 0660 (the deftype variant-ctor / field / platform enumeration cells,
  §3.3) — **actioned + DELETED S114 Phase 3**: spec scribed, design enumerated,
  all four cells implemented. (FIXME 0651, the deftrait method-name enumeration
  gap, was likewise actioned by /spec and deleted — §5 intro + §5.3.3 scribe it.)
- `design/frontend/enforcement-matrices.md` — the sibling S114 Track-D doc: the
  BD-A operand-position one-seam + the RA dangling-qualifier/bound-form-type
  reject (annotation/reference family, NOT binder heads) + deftype-ctor trailing.
  The value-level binder re-landing (§3.4) is this doc's; BD-A/RA are that one's.
- `crates/cranelisp-frontend/src/ast_builder.rs:111` — `reject_qualified_binder_head`
  as landed (the both-halves-non-empty §8.5-dual predicate; FIXME 0659 realigned §2).
- SPRINT.md §"Architecture review" Q3 — the `/arch` ruling this designs against.
