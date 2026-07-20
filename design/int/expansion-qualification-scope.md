# Expansion-pass qualification is scope-aware — binders are never qualified (S114 Track C, FIXME 0670)

> Subordinate topic doc, cited from `design/int/int.md` and the CLAUDE.md
> macro-expansion section. Owned by `/design`(int). Authored S114 Phase 3 against
> SPRINT.md §Scope-C + the `/arch` path-1 ruling
> (`design/arch/fixmes/0670-*.md` §RULING) + SPRINT.md §Architecture-review F8
> (three waves, strict order). Pairs with `design/frontend/binder-head-reject.md`
> (the frontend value-level reject that re-lands in wave 2).
>
> **Status: DESIGN, pre-implementation.** The seam is `qualify_expanded_sexp`
> (`src/process_form/macro_resolution.rs:431`); the fix is to make it
> scope-aware, structurally mirroring the expander's own binder handling.

## 1. The defect — a scope-blind qualify pass mirrors a scope-aware expander

After a cross-module macro expands, int runs a **name-qualification hygiene
pass** so bare references to the macro's defining module resolve for the consuming
module's typechecker: `qualify_expanded_sexp` walks the expanded Sexp and rewrites
any bare symbol found in a `defining_modules` table to `<home>/<name>`. It runs
only when `defining_modules` is non-empty (a foreign macro was expanded) —
`macro_resolution.rs:412-416`.

The pass is **scope-blind**. It recurses into every `List`/`Bracket` child and
qualifies any bare symbol it finds in a defining module — including
**binder positions** and **local reads**. So:

```clojure
(defn greet [name] (str "hello, " name))   ; `str` is a macro; `name` collides with an importable symbol
```

expands (correctly, param bare) and is then re-walked by `qualify_expanded_sexp`,
which rewrites the **param binder** `name` → `primitives/name` (and the body read
`name` likewise). The frontend then rejects `primitives/name` at the param
("a binder must be bare"). The bug triggers ONLY when (a) the binder name collides
with an importable symbol AND (b) a macro is in scope (so this pass runs at all).

This is the **P7 mirror** the project fights: two walks over the same tree, one
(`expand_scoped`) carefully scope-aware — it tracks `shadows` so binders and local
reads are held verbatim — and a second (`qualify_expanded_sexp`) scope-blind,
re-introducing exactly the confusion the first walk avoided. `qualify_expanded_sexp`
even *documents* head-skipping ("Don't qualify the head of special forms like
defn, let") that it does **not** implement, and has no binder concept at all.

**`/arch` path-1 ruling:** a binder is never a reference; qualification is a
**resolution-product** operation and a binder position produces no resolution
product (Principle 24 corollary — only *references* carry resolved identity; a
binder *introduces* a name). The expansion pass MUST skip binder slots.

## 2. The seam — thread a scope, reuse the expander's binder enumeration

`qualify_expanded_sexp` gains a lexical-scope parameter and consults it exactly as
`expand_scoped` does. The two walks must share **one** scope model (Principle 7),
not grow a second binder enumeration.

### 2.1 The rule

> Qualify a bare symbol **iff it is a free reference** — not lexically bound by an
> enclosing scope. A symbol in the current `shadows` set is either a **binder**
> (its introducing position) or a **local read** (a reference to that binder); in
> both cases it must be held **verbatim**, never qualified.

Threading the scope fixes *both* faces at once:

- the **binder** `name` in `[name]` is in scope → held bare (the 0670 reject
  disappears);
- the **local read** `name` in the body is in scope → held bare (this is the
  latent second face that *masked* the bug pre-S113 — the body read was
  mis-qualified *consistently* with the param, so the program ran; both faces are
  now correct);
- a genuine **free** reference to a defining-module symbol (the macro's expanded
  helpers, e.g. `str-concat`/`show`) is NOT in scope → qualified, as required.

### 2.2 Shape of the change (mirror `expand_scoped`/`expand_binding_form`)

`qualify_expanded_sexp` takes `shadows: &HashSet<String>` (public entry seeds it
empty). Its arms become:

- **`Symbol(name)`** — first guard: `if shadows.contains(name) { return verbatim }`
  (added ahead of the existing already-qualified/annotation/`_`/`current-module`
  skips). This one line is the binder-and-local-read skip.
- **`List` with a binding-form head** — dispatch to a binder-aware handler that,
  for each binding special form, (a) holds the **binder positions** verbatim,
  (b) accumulates the introduced names into the scope, and (c) qualifies the
  **value/body** children under the *extended* scope. This mirrors, one-to-one,
  the expander's `expand_binding_form` → `expand_let`/`expand_fn`/`expand_defn`/
  `expand_match` structure.
- **`List` (non-binding) / `Bracket`** — recurse into children under the current
  (unchanged) scope, as today.

### 2.3 The binder-position enumeration (0660 completeness — every value-level slot named)

The value-level binder slots §5 governs, and how the walk identifies them — these
MUST be complete across the walk, each named in the change-set or a legal skip:

| Form | Binder slots (held verbatim) | Reference slots (qualified under extended scope) |
|---|---|---|
| `defn` / `defn-` | the **name** (2nd elem); each **param** — every bare non-annotation symbol in the `[…]` bracket | the body |
| `fn` / `lambda` | each **param** in the `[…]` bracket (bare non-annotation) | the body |
| `let` | each **binding name** — the name half of each `[name val …]` pair in the bind bracket (added to scope *sequentially*, `let*`, before its own value is qualified) | each binding **value** (under the scope accumulated so far); the body |
| `match` | each **pattern variable** — a bare lowercase symbol pattern, and the non-head symbols of a constructor pattern `(Ctor v …)`; `_` and uppercase (nullary ctor / ctor head) bind nothing | the scrutinee (outer scope); each arm body (under the arm's pattern scope) |

**Reuse, do not re-derive.** These are exactly the predicates the expander already
owns: `is_binding_form`, `params_scope`, `pattern_binders`, `is_annotation_symbol`,
`starts_uppercase` (`src/expander.rs:963-1032`). Promote them to a shared home
(`pub(crate)`, or a small `expander::scope` module) and have **both** walks call
them, so a future binder-form addition updates one enumeration and both walks stay
in lockstep. A second private copy of the binder rules in `macro_resolution.rs`
would be the very P7 mirror this fix removes.

**Legal skips named:** `deftype`/`deftrait`/`defmacro`/`mod`/`platform`/`import`/
`export` binder positions are **not** reached by this pass in the value-level way —
their binder rejects already land at the raw/earlier layer (0670 §"Landed in W3":
deftype ctor/field, defmacro params, module aliases). This pass handles only the
value-level scoping forms above; the walk falls through non-binding heads
structurally, so a form it does not special-case is qualified as ordinary children
(correct — those forms carry no value-level binder the pass could mis-qualify).

## 3. The mandatory expansion-seam unit test (`/arch`-named, METHOD §2.2)

Pure, no session — feed a pre-expanded/qualified fixture through the pass:

- **`qualify_skips_value_binders_and_local_reads`** — input the expanded shape of
  `(defn greet [name] (<foreign-helper> "hi" name))` where `name` is present in a
  defining module. Assert: the **param** `name` stays **bare**; the **body read**
  `name` stays **bare** (local); the **foreign helper** head **is** qualified to
  its defining module. Fail-on-revert: with the scope-blind pass the param
  qualifies to `<home>/name`.
- **`qualify_skips_let_and_match_binders`** — `(let [name "x"] (m name))` and a
  `match` arm binding `name`: binder + local read bare; a free defining-module
  reference qualified.
- **completeness twin** — one cell per binder form (defn/fn/let/match) so the
  matrix pressures the ONE shared enumeration (the coverage-by-variants lens).

## 4. Handoff contract to the frontend re-landing (wave 2, F8 strict order)

The consequent chain is three waves, strict order (SPRINT.md F8):

1. **This int fix (wave 1)** establishes the invariant: **no binder position in
   `qualify_expanded_sexp`'s output carries a `/`** — expansion-side name
   qualification operates on references only. (`/arch` records this durably at
   `design/arch/bounded-contexts.md` §6, macro-execution area.)
2. **Frontend value-level reject re-lands (wave 2, Track D)** at the three
   reverted seams — `build_annotated_params`, `build_let_bindings`,
   `build_pattern` — now firing **only** on user-written qualified binders
   (`(defn f [a/b] …)`), never on int's output. The contract wave-1 gives it: any
   qualified binder the frontend sees is **user-authored**, because int no longer
   produces one.
3. **`/testing` cells (wave 3)**: the IQ-P1..P3 positives (collision + macro
   compiles) + the IQ-N1..N4 value-level qualified-binder negatives
   (`tests/plan/s114-test-plan.md` §4.3).

**Sequencing is load-bearing.** If the frontend reject re-landed **before** the
int fix, it would reject int's mis-qualified binders and break valid programs
(exactly why W3 reverted it). Int-first is mandatory; the two surfaces are one
logical wave over two `/dev` deployments (the `quote-shield.md` / 0613 precedent).

## 5. Principles cited

- **Principle 24 (corollary)** — only references carry resolved identity; a
  binder introduces a name and is never a resolution product to qualify.
- **Principle 7 / Principle 19** — one scope model shared by both walks; no
  second binder enumeration, no name-privileged special-case; the reject stays
  single-sourced in the frontend (this pass only *stops producing* the bad input).
- **Principle 18** — binders identified structurally (bare non-annotation symbol
  in a binder slot), not by a name/kind heuristic.
- **Principle 5** — the pass is a pure `(sexp, scope) → sexp` transform,
  unit-testable without a session (§3).

## 6. Cross-references

- `src/process_form/macro_resolution.rs:431` (`qualify_expanded_sexp`) — the seam;
  `:412-416` — its call site (runs only when `defining_modules` is non-empty).
- `src/expander.rs:963-1032` (`is_binding_form`, `params_scope`, `pattern_binders`,
  `is_annotation_symbol`, `starts_uppercase`) + `expand_scoped`/`expand_binding_form`
  — the scope model to share.
- `design/frontend/binder-head-reject.md` — the paired frontend reject (wave 2).
- `design/arch/fixmes/0670-*.md` — the `/arch` path-1 ruling this designs against.
- `design/arch/bounded-contexts.md` §6 — where `/arch` records the durable
  "expansion qualifies references only, never binders" invariant.
- `tests/plan/s114-test-plan.md` §4.3 (IQ-P1..P3 / IQ-N1..N4) — the e2e chain.
- `spec/05-definitions.md` §5 — the value-level binder-position table (bare where
  written); FIXME 0683 corrected §5's reader-reject wording (accuracy).
