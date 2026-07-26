---
number: 0907
target: /design (backend)
filed_by: /qa
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-backend/src/drop_glue.rs:497-505 (ctor_shapes identity check);
  src/bootstrap.rs:767-783 (the seeded Bind ctor scheme);
  crates/cranelisp-intrinsics/src/drop.rs::free_io_branches (the live runtime IO-tree owner);
  design/backend/transitive-drop-glue.md §4.1; design/arch/fixmes/0903-*.md (sibling class);
  tests/plan/s118-test-plan.md §11 (attribution record)
status: open
---

# `IO`'s existential `Bind` ctor defeats canonical per-concrete glue derivation — every release of a concrete `IO T` value hard-refuses

## Severity

Important — 7 committed e2e cells RED (`spec_10_io` ×3, `ctor_as_value` ×2,
`examples` ×1 [two example programs: 21-hello-io, 23-io-sequence],
`stdlib_conformance` ×1 [core.io/when-io, taking `core` and `core.io` down]),
and the whole class of user programs with an IO-typed *binding or temporary*
(any IO combinator: `when-io`, `then`, `map-io`) refuses to compile.

## Minimal repro (one line, PrimitivesOnly prelude, verified at HEAD `49a20269`)

```
(match (Pure 5) [(Pure x) x (Effect e) 0])
→ Error: codegen failed for user/__expr: codegen error at 0..0:
  constructor 'Bind' disagrees on declared parameter identity for 'primitives/IO'
```

Scope-exit face, same signature:

```
(defn f [] (let [x (Pure 5)] 1))
```

Any release site of a concrete `IO T` value reproduces it — the match
temporary-scrutinee dec and the scope-exit dec both route through
`emit_typed_rc_dec` → `DropGlueRegistry::request_if_owning(IO(Int))`.

## Mechanism (attributed, read at source — two layers)

1. **The proximate error.** `drop_glue.rs::ctor_shapes` builds one shared
   substitution over ALL of a type's constructors and hard-errors when two
   ctors' result-type ADT args bind different `TypeId`s (`existing !=
   &ctor_subst`, :497-505). `Pure`/`Effect` are seeded through
   `register_synth_adt` sharing `Var(io_a)`; `Bind` is seeded MANUALLY
   (`src/bootstrap.rs:767-783`) with fresh `bind_a`/`bind_b` — an intentional
   existential encoding ("HM cannot express the existential, so Bind bypasses
   the normal ctor scheme path"). The identity precondition is therefore
   structurally unsatisfiable for `primitives/IO`; the check fires on the
   first concrete `IO T` glue request, always.

2. **The deeper fact — a per-ctor substitution does NOT fix it.** Even
   substituting each ctor's own result vars positionally, `Bind`'s field
   types (`inner: IO b`, `cont: Fn [b] (IO a)`) keep `Var(bind_b)` free:
   the existential `b` is not determined by `IO a`'s parameter, so
   per-concrete static glue for `IO T` cannot type Bind's fields from ctor
   shapes at all. This is a modelling gap, not an implementation slip.

## Why it surfaced at W3 (honest provenance)

The S116 registry had **zero consumers** until W3 (the D1 borrow-conflict
finding), so `ctor_shapes` was unreachable and these programs compiled —
IO-typed scope releases went through the legacy inline emitter, which did
not derive IO glue this way (silent shallow teardown, the leak direction).
W3's migration routed every typed release through the registry and turned
the silent-wrong into loud-refusal — D2's no-fallback discipline working as
designed on a type it cannot yet model. These 7 REDs are therefore
W3-surfaced (not in the sprint-open 28; proven not-W4's by stash/pop at the
W4 review). A revert is not the fix; a ruling is.

## Relation to FIXME 0903 — same class, third face

0903's two censused escapee families (synthetic accessors of
generic/undeclared-field products; generic trait-method instances) reach the
release machinery with *residual signature vars* and silently leak. The
IO/Bind face reaches it with an *existential ctor field* and loudly refuses.
One class: signature-driven, compiled-once artifacts whose field/parameter
types are not determined by the concrete type the release is keyed on. The
`/design`(backend) ruling 0903 already owes should co-rule this face — ruling
the accessor/trait families without IO leaves the loudest member unfixed.

## Candidate directions (for the ruling; none costed here)

- **Route IO to the runtime teardown owner.** `cranelisp-intrinsics` already
  owns dynamic, tag-directed IO-tree teardown (`drop.rs::free_io_branches`,
  three call sites, incl. the PAR branch walk); a closure field is already
  dynamically releasable via its embedded `DROP_GLUE_PTR`. The registry
  would classify `primitives/IO` as runtime-owned and emit a call to the
  intrinsic instead of deriving ctor shapes. Note `Pure`'s payload (`a`) is
  the one field that IS determined by the concrete arg — the ruling must say
  who discharges it and how the runtime knows its category.
- **Per-ctor substitution + dynamic escape hatch for existential fields** —
  relax the identity precondition to positional per-ctor mapping and give
  unresolvable fields a dynamic disposition (closure via embedded ptr; ADT
  fields would need information that does not exist without a header
  type-word, rejected R15). Likely unsound for the general case; recorded
  for completeness.
- **Special-case exclusion at admission** (`HeapCategory`/registry refuses
  to own IO; the S116-era behaviour) — restores compilation but restores the
  silent leak too; if taken it MUST land with a failing-not-ignored leak
  guard so the leak stays visible.

## Sequencing

`/qa` recommends the ruling ride the S119 0903 window (`/design`(backend),
with `/arch` adjacency: IO is seeded by int's bootstrap, torn down by
intrinsics, refused by backend — three contexts meet here). Until then the 7
cells are attributed carries; `tests/plan/s118-test-plan.md` §11 carries the
name-for-name list.

## REPL-experience evidence (appended by `/repl`, S118 Phase 6a)

Added at `/sprint`'s request rather than filed as a duplicate. Three things the
attribution above does not record, all measured at the prompt at HEAD `4ed43430`.

### 1. The blast radius at the prompt is narrower than "IO refuses"

This matters for the ruling's urgency and for what a user can be told meanwhile.
`07-io-and-effects.demo` — the guided arc's whole IO chapter — **replays green**.
Everything a user meets first still works: `(platform stdio)`, `print`,
`(do …)`, `(bind! [x …] …)`, `(Pure 42)`, `(bind (Pure 10) (fn [x] …))`, an
effect-returning `defn` with inferred `(IO Int)`, and `if` selecting between two
effects. The refusal needs an IO value to reach a **release site**: a `match` on
IO constructors, an IO-typed `let` binding, or a user-defined combinator over
`(IO a)`. So the reachable-by-a-beginner surface is intact, and the shapes that
refuse are the ones a user reaches when they start *abstracting* over effects —
writing their own `then`/`when-io`/`map-io`. That is a bad place to hit a wall
(it is the first genuinely creative thing a user does with effects) but it is not
the first ten minutes.

### 2. It takes an archived regression guard down

`repl/demos/archive/ring4s.demo` is RED, at exactly its `(defn then [a b] (bind a
(fn [_] b)))` + `(then …)` segment — a demo written in S61 to guard the *previous*
IO-combinator double-free. The segment is retained failing on purpose with an
attribution comment naming this FIXME (`repl/demos/CLAUDE.md` §archive records
the attribute-don't-repair rule). It is the archive's only red and it flips when
this is ruled. Note the shape it guards: `(fn [_] b)` returning a captured IO
value is the *same* idiom whose double-free S61 fixed, so this segment is
load-bearing history, not incidental.

### 3. The definition/call asymmetry is itself confusing

```
> (defn then [a b] (bind a (fn [_] b)))
:(Fn [(primitives/IO a) (primitives/IO b)] (primitives/IO b)) user/then ; defn
> /sig then
:(Fn [(primitives/IO a) (primitives/IO b)] (primitives/IO b)) user/then ; defn
> (then (Pure 1) (Pure 2))
Error: codegen error at 0..0: codegen failed for user/user/then$primitives/IO$Int+primitives/IO$Int: ...
```

The definition is accepted, echoes a correct polymorphic signature, and
introspects cleanly through `/sig`. Only instantiation refuses. From the prompt
this reads as "the function exists and is well-typed, but calling it is
impossible" — the user has no way to tell that the obstruction is per-concrete
release-code derivation, and nothing in the surface suggests the shape is
unsupported *before* they write it. If the ruling ends up at the "special-case
exclusion at admission" option, consider whether the refusal should move to the
**definition** so the feedback arrives where the user can still change course.

### 4. Recovery is clean (the one unambiguous good news)

`repl/spec.md` §5.2 holds. After each refusal the session is intact: `(+ 1 2)` →
`:primitives/Int 3`, a following `defn` compiles and runs. No poisoning, no
cascade. The S117 failed-codegen transaction work is doing its job here.

### 5. The diagnostic's nouns are undiscoverable — and inconsistently so

```
> Bind
Error: type error at 0..4: undefined variable: Bind
> /info Bind
error: unknown symbol 'Bind'
> /info IO
error: unknown symbol 'IO'
> Pure
:(Fn [a] (primitives/IO a)) primitives/IO.Pure ; deftype
```

The message names a constructor `Bind` and a type `primitives/IO`; the REPL then
denies both exist — while `Pure`, the *sibling constructor of the same type*,
introspects correctly. This traces straight to the mechanism above: `Pure` and
`Effect` go through `register_synth_adt` and land as ordinary entries, `Bind` is
seeded manually at `src/bootstrap.rs:767-783` and evidently not enrolled the same
way. So the introspection asymmetry and the glue refusal have **one cause**, and
whatever the ruling does about `Bind`'s scheme should make it introspectable —
a user told to reason about `Bind` must be able to look it up.

`/info IO` failing is a separate small gap worth catching in the same window: the
type is nameable in a signature (`(primitives/IO a)` prints in every `defn` echo
above) but not introspectable.

The *frame* the message is rendered in — degenerate `0..0` span, doubled
`codegen error at 0..0:` prefix, `user/user/` doubling, and the `$`-mangled
instance name — is **not** specific to this defect and is filed separately as
FIXME 0915 with `repl/spec.md` §5.5 as the new normative contract. Items 1–5
here are the IO-specific half.

## Stdlib evidence (appended by `/stdlib`, S118 Phase 6a)

Appended per `/sprint`'s dispatch rather than filed as a duplicate. The
library-author half: what the refusal costs, and the falsification of the
"just re-spell it" option that a reader of this FIXME would otherwise try.

### 1. Conformance gate reconciled name-for-name — 36 of 38

`stdlib_conformance::stdlib_all_public_modules_compile_and_run` (78 s, cold
per-module subprocess loop) reports **two** modules, one cause: `core.io`
(`codegen failed for core.io/when-io`) and its parent shell `core`
(transitive — `core.cl` declares `(mod io)`). The other 36 are green; the
three `def`/`const` binder rows in the same binary are green. So the
severity block's "×1 [core.io/when-io]" is one *cause* but **two named
modules** in the aggregated report — worth knowing at the ruling's
acceptance, since both flip together.

Blast radius *inside* `stdlib/` is exactly those two: the prelude does not
re-export `core.io`, and `derive`/`derive.helpers` reach `core.syntax`
directly rather than through the `core` shell. `io.monad` — the prelude's
`pure`/`do`/`bind!` — is **green**, which is the mechanism behind `/repl`'s
item 1: a beginner's first effects work; what breaks is the first attempt to
*abstract* over effects, which is what all six `core.io` combinators are.

### 2. The trigger inside `when-io` is the MIXED `if` arm (narrowed)

`when-io` contains no `bind` at all — `(if cond io-action (Pure 0))`. Probes
at HEAD `e67857ce` (one file, PrimitivesOnly, `--no-cache`):

| Shape | Result |
|---|---|
| `(defn f [] (Pure 0))` | compiles — returned concrete IO transfers, no release |
| `(defn g [c] (if c (Pure 1) (Pure 0)))` | **compiles** — both arms fresh |
| `(defn i [io] (if true io (Pure 0)))` | refuses |
| `(defn j [c io] (if c io (Pure 0)))` | refuses — this is `when-io` |
| `(defn h [] (let [x (Pure 5)] 1))` | refuses (the §"Minimal repro" scope-exit face) |
| `(defn pick [c b] (if c b (MkBx 0)))` over an ordinary user ADT | **compiles** |

So the `if`-join is not itself the trigger: two freshly-constructed arms
returned are fine. The refusing shape is **one borrowed-parameter arm joined
with one freshly-built concrete arm** — and the identical shape over a
non-IO heap ADT compiles, which independently confirms the attribution is
IO/`Bind`-specific and not a general mixed-arm release defect (i.e. it is
not 0726's axis).

### 3. There is NO legal re-spelling — the workaround option is falsified

This is the load-bearing finding for the ruling's urgency.

| Shape | Definition | Concrete call |
|---|---|---|
| `(defn >> [a b] (bind a (fn [_] b)))` | compiles | **refuses** (`>>$primitives/IO$Int+primitives/IO$Int`) |
| `(defn map-io [f io] (bind io (fn [x] (Pure (f x)))))` | compiles | refuses |
| `(defn wi3 [c a alt] (if c a alt))` — polymorphic `when-io` | **compiles** | **refuses** (`wi3$Bool+primitives/IO$Int+primitives/IO$Int`) |

The four combinators that are *polymorphic* (`>>`, `map-io`, `timeout`,
`sequence-io`) already compile in `core.io` — they refuse only when a user
instantiates them. `when-io`/`unless-io` refuse earlier only because they
name a concrete `(Pure 0)` in their own bodies. Re-spelling `when-io`
polymorphically therefore **compiles the module and leaves the capability
exactly as broken**, while removing the only signal the conformance gate
has. `/stdlib` has consequently declined to land any workaround: `core.io`
stays red as the honest record, with the measured detail and the six
withheld self-tests enumerated in `stdlib/core/io.cl`'s header (per
`stdlib/CLAUDE.md`'s ceilinged-coverage convention), and the assessment in
`stdlib/plan-stdlib.md` §28.2.

**Implication for the ruling's option 3** ("special-case exclusion at
admission", which restores compilation and the silent leak): from the
library-author side that option is the *only* one that makes the six
combinators reachable again, and it would restore a leak on every IO value
a user's own combinator releases. If it is taken, the failing-not-ignored
leak guard the option already requires should include a **stdlib-shaped**
cell (a user-defined `then`/`when-io` over `(IO a)`, not just a bare
`(Pure 5)` release), because that is the shape the leak actually reaches in
production.

### 4. Acceptance rider for the fixing change-set

`core.io` has no `(mod- test)` today — untestable while refused. The six
withheld cases (`>>`, `map-io`, `when-io`, `unless-io`, `sequence-io` over
`Nil` and a 3-element list, `timeout` both arms incl. loser cancellation)
are enumerated in the module header as a restore list; `/stdlib` lands
`stdlib/core/io/test.cl` in the same window the ruling's fix lands, and the
`stdlib_conformance` red flips from 2 modules to 0.
