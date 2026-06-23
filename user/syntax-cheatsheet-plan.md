# `/syntax` Cheat-Sheet — Content Plan (Sprint 90, Pillar 1)

> **Status**: PLAN (Phase 3 DESIGN). This document is the content plan for the
> `/syntax <topic>` cheat-sheet. It is owned by `/docs`. It pins the **topic
> taxonomy**, the **per-topic dense format**, the **verified-compiling method**,
> and the **asset shape**. The full cheat-sheet content is authored in Phase 5
> (verified-compiling), validated by `/spec` as a Phase-5 gate.

## 1. What this is and who reads it

The `/syntax` cheat-sheet is a **token-dense, example-driven projection of the
spec** — a curated syntax reference, organized by topic, surfaced as a REPL
command useful to **both the human REPL user and the embedded agent**
(self-documenting-REPL principle).

- **Human:** types `/syntax cond` at the REPL to recall the exact `cond` shape.
- **Agent:** prompted with a syntax question it can't ground, pulls
  `/syntax <topic>` (a read-only command) instead of guessing — the primer's
  topic cross-reference (Pillar 1.3, `/dev`-wired) tells it which topics exist.

It is a **projection of `spec/`** — no normative content of its own. Where the
cheat-sheet and the spec disagree, the spec wins and the cheat-sheet is the bug.
Each topic **cross-links its spec section(s)** so the precise rules keep one home
(the `user/CLAUDE.md` cross-link-don't-restate convention).

**It is NOT prelude/stdlib idiom-baking.** Core-language syntax derived from spec
is the primer-appropriate kind of grounding. Prelude/stdlib symbol awareness stays
**harvest-sourced** (memory `agent-prelude-awareness-via-harvest-not-primer`,
S90 Pillar 2). The cheat-sheet covers *language syntax* (special forms, type
syntax, definition forms, the macro-writing surface). The handful of
**prelude-provided macros** it documents (`cond`, `do`, `->`, `bind!`, …) are
included because they are *syntactic constructs a user reaches for by shape*,
clearly tagged `[prelude macro]` so the reader knows they are not core and not
guaranteed by an empty prelude.

## 2. Topic taxonomy

Topics are sized so each is a **coherent token-dense unit the agent pulls by
name**. ~24 topics, grouped. Each maps to its spec section(s). Names are
kebab-case CLI keywords. A topic may cover a small family of related forms (e.g.
`deftype` covers product/sum/enum/shortcut) — the unit is "what you look up in
one go", not one-form-per-topic.

### Core language — special forms & expressions

| Topic | Covers | Spec anchor(s) | Tier |
|---|---|---|---|
| `defn` | `defn`/`defn-`, single-sig, docstring, param annotations, discard `_`, auto-curry | 05 §5.1.1, §5.1.3 | core |
| `defn-multi-sig` | multi-signature `(defn name ([p] b) ([p q] b))`, `$`-mangling, dispatch | 05 §5.1.2; 04 §4.7 | core |
| `let` | `(let [x e ...] body)`, sequential visibility | 04 §4.3; 02 §2.3.3 | core |
| `if` | `(if cond then else)`, both branches required | 04 §4.4 | core |
| `fn` | `(fn [params] body)`, param annotations, closures, auto-curry | 04 §4.5; 02 §2.3.5 | core |
| `match` | `(match e [pat body pat body ...])` — **flat bracket pairs** | 06 §6.1; 04 §4.8 | core |
| `patterns` | ctor-data `(Ctor v ..)`, nullary, wildcard `_`, var; exhaustiveness | 06 §6.2, §6.5 | core |
| `annotations` | `:Type form` binds following form (all positions); REPL `:Type value` | 04 §4.9; 02 §2.3.8; 01 §1.4.5 | core |
| `vectors` | `[a b c]`, `[]`, element-type uniformity, `(vec ..)` | 04 §4.10; 02 §2.3.9 | core |
| `recursion-tco` | self-recursion (no `recur`), tail position, accumulator idiom, TCO guarantee | 04 §4.x; appendix-c (TCO NFR) | core |
| `trace` | `(trace expr)` → Trace ADT | 04 §4.12; 02 §2.3.10 | core |

### Core language — types

| Topic | Covers | Spec anchor(s) | Tier |
|---|---|---|---|
| `types` | primitives `Int`/`Bool`/`String`/`Float`, named, applied `(Option Int)`, type vars | 03 §3.1, §3.2.2; 02 §2.4 | core |
| `fn-type` | `(Fn [T1 T2] R)`, nullary `(Fn [] R)` | 03 §3.2.1; 02 §2.4.5 | core |
| `hkt` | higher-kinded type application `(f a)`, kind `* -> *`, HKT trait/impl targets | 03 §3.7; 07 §7.2, §7.3.4 | core |
| `constraints` | constrained polymorphism `(Fn [:Num a] a)`, inferred trait bounds | 03 §3.4; 07 §7 | core |

### Core language — definitions

| Topic | Covers | Spec anchor(s) | Tier |
|---|---|---|---|
| `deftype` | product, sum, enum, shortcut, docstrings, generated accessors, `deftype-` | 05 §5.2 | core |
| `adt` | constructors (nullary value / data fn), `match` over them — the ADT *usage* view | 05 §5.2.2; 06 §6.2 | core |
| `traits` | `deftrait`, method sigs, `self`, default methods, `deftrait-`, built-ins (Num/Eq/Ord/Display/Functor) | 07 §7.1, §7.7 | core |
| `impl` | `impl` concrete / ADT-instance / polymorphic / HKT; no `impl-` private; no method docstrings | 05 §5.4; 07 §7.3 | core |

### Core language — macros, modules, IO

| Topic | Covers | Spec anchor(s) | Tier |
|---|---|---|---|
| `defmacro` | single/multi-clause, `& rest`, `defmacro-`, Sexp/SList, quasiquote `` ` ~ ~@ ``, auto-gensym `x#` | 09 §9.2, §9.4, §9.8; 05 §5.5 | core |
| `modules` | `(mod ..)`/`mod-`, qualified `module/name`, dotted `Type.Ctor`, `platform` decl | 08 §8.1, §8.2, §8.5 | core |
| `import` | specific / glob `[*]` / member-glob `[Type.*]` / alias `(mod a)` / rename `(src local)` / `super` / null `[]` | 08 §8.3 | core |
| `export` | `(export [mod [names]])`, glob, mount `(mod alias)` | 08 §8.4 | core |
| `io` | `IO` type, `pure`/`bind`, `do`, `bind!`, `(defn main [] ..)`, `platform` | 10 §10.1–§10.6 | core + prelude macros |

### Prelude macros (syntactic constructs, tagged `[prelude macro]`)

| Topic | Covers | Spec anchor(s) | Tier |
|---|---|---|---|
| `cond` | `(cond t1 b1 t2 b2 default)` — **flat pairs + mandatory default**; NOT Clojure clauses | 09 §9.10.8 | prelude macro |
| `threading` | `->` thread-first, `->>` thread-last | 09 §9.10.6–7 | prelude macro |
| `do-bind` | `do` sequence, `bind!` monadic-bind sugar, `let`-vs-`bind!` | 09 §9.10.4–5; 10 §10.4–5 | prelude macro |
| `prelude-sugar` | `def`, `const`, `list`, `vec`, `str`, `case`, `when` — short reference + tag | 09 §9.10 | prelude macro |

> **Notes for the author (Phase 5):**
> - `adt` vs `deftype`: `deftype` is the *declaration* view; `adt` is the
>   *usage* view (construct + match). Keep them distinct but mutually
>   cross-referenced — the agent pulling `adt` wants "how do I make and take
>   apart a value", not the full declaration grammar.
> - Bare `/syntax` lists topic names + one-line glosses (the UX is `/repl`'s,
>   §17; this plan supplies the gloss text per topic).
> - Consider an alias map (e.g. `/syntax lambda` → `fn`, `/syntax struct` →
>   `deftype`) — a `/repl` UX call, flagged below.

## 3. Per-topic dense format

Each topic is **one compact block**: a gloss, the canonical form(s), 1–2 minimal
verified examples, NOT-equivalents where the model's training misleads, and a
spec cross-link. Token-dense (it lands in an LLM context) but human-readable (it
is also a REPL command). Skeleton:

```
TOPIC <name>  [core | prelude macro]
  <one-line gloss>

  FORM
    <canonical syntax form(s), exactly as spec writes them>

  EXAMPLE
    <1-2 minimal forms that COMPILE — verified via live REPL>

  NOT            (only where the model's training misleads — omit otherwise)
    <the wrong-but-tempting shape> -> <the Cranelisp shape>

  SPEC  <file §section>[, <file §section>]
```

Rules:
- **Forms use the spec's exact bracket/paren shapes.** Load-bearing: `match`
  arms are **flat pairs in one `[ ]`** (`[Red "r" Green "g"]`), while multi-sig
  `defn` variants are **paren-grouped** `([p] b)`. The cheat-sheet must not blur
  these — getting the bracket shape wrong is the single highest-value thing a
  syntax reference prevents.
- **Examples are minimal and self-contained** — the smallest form that
  demonstrates the construct and compiles. Reuse the spec's own examples where
  they are already minimal (they are the validated source); shrink where not.
- **`NOT` lines only when the model will reach for the wrong idiom** (the primer
  already does this for `recur`/`zero?`/`cond`/`defun` — the cheat-sheet extends
  it per-topic, e.g. `match` paren-clauses, Clojure `cond`). Keep them to one
  line each; do not pad.
- **Prelude-macro topics carry the `[prelude macro]` tag** and a one-line
  "not core; absent under empty prelude" note, so the reader never mistakes them
  for guaranteed syntax.
- **No internal type-variable names** (`a0`, `t42`) ever surface
  (`user/CLAUDE.md`).
- **Type display follows `:Type value`** with fully-qualified names where shown
  (e.g. `:primitives/Int 3`, `:(Fn [a] a) user/id`).

The bare `/syntax` index entry per topic = the topic name + the one-line gloss
(reuse the gloss column of §2). The `/repl` owner formats the index list.

## 4. Verified-compiling method (S89 load-bearing discipline)

**Every example in the cheat-sheet MUST compile via the live REPL before it
ships.** This is the same verified-compiling discipline S89 made load-bearing for
the primer idioms. A cheat-sheet that teaches a non-compiling form is worse than
no cheat-sheet — it actively misleads both the human and the agent.

Phase-5 authoring procedure (per topic):
1. Draft the topic block with examples sourced from the spec section (the spec's
   own examples are already validated against the implementation — start there).
2. Run **each example** through the live REPL (build the binary, feed the form,
   confirm it type-checks and produces the expected `:Type value`). Examples that
   need a platform/IO context (e.g. `io`, `main`) run via `--run` on a minimal
   file rather than the bare REPL.
3. Any example that does **not** compile is either (a) corrected to the
   compiling shape, or (b) if it *should* compile and does not, it is a
   **defect** — handed to `/qa` for a narrow failing repro (root `CLAUDE.md`
   §"Usability Findings and Defects"; `/docs` work is not closed until the test
   exists). Do not ship a "known-broken" example.
4. Record the verification (which examples were run, expected output) alongside
   the content so re-verification on spec drift is cheap.

**`/spec` validates content accuracy as a Phase-5 gate** (S90 /arch R7: content
= /docs, validated by /spec; a projection of spec, no normative change). `/spec`
confirms each topic's forms and cross-links match the current spec; `/docs`
confirms each example compiles. Both gates pass before Pillar 1 closes.

> **Phase-3 finding already surfaced (for /spec's Phase-5 validation):** the
> always-on primer (`src/agent/primer.txt`) currently shows the `area`/`match`
> example with **paren-grouped arms** `((Circle r) (* ..))` (lines ~122–125) and
> the multi-sig/sum-ctor examples likewise — but the spec's authoritative `match`
> grammar (06 §6.1) is **flat bracket pairs** `[(Circle r) (* ..) (Rect w h)
> (* w h)]`. The cheat-sheet `match`/`adt`/`impl` topics will use the spec
> (bracket) shape. If the primer shape is also wrong (vs. as-built compiler),
> that is a primer defect for `/dev` + a `/qa` repro, not a cheat-sheet matter —
> flagged here so Phase 5 reconciles the two against the live REPL rather than
> shipping two contradictory shapes. **Resolve by running both shapes through the
> REPL during Phase-5 verification** and conforming to whatever compiles (then,
> if the spec example itself fails, escalate to /spec/qa).

## 5. Asset shape (coordinate with `/dev (src/)`)

Per /arch R7 the content ships as a **static asset `include_str!`'d by `src/`**
(mirrors how `primer.txt` is `include_str!`'d by `src/agent/primer.rs`).

**Recommendation: one file with topic delimiters**, located at
`src/syntax/cheatsheet.txt` (sibling to the existing `src/agent/primer.txt`
pattern). Rationale:

- **One `include_str!`** is the simplest wiring for `/dev` — a single embedded
  string parsed at load into a `topic -> block` map by a stable delimiter.
- **One file is easiest for `/docs` to author and re-verify** as a unit, and for
  `/spec` to validate in one pass.
- A machine-stable **delimiter line** separates topics, e.g.:

  ```
  === topic: cond ===
  <block>
  === topic: match ===
  <block>
  ```

  The delimiter carries the canonical topic keyword; the index command (`bare
  /syntax`) is derived by scanning delimiters + the first gloss line, so the
  topic list never drifts from the content.

- **Not feature-gated.** `/syntax` is a normal REPL command useful to the human
  independent of the `agent` feature — the content asset and command live on the
  default path. (Only the agent's *pull* of `/syntax` rides the `agent` feature;
  the command itself does not.) This matches /arch's "static `include_str!`
  asset + read-only command" framing.

`/docs` owns the **content** of `src/syntax/cheatsheet.txt` (the blocks). `/dev`
owns the **wiring** (the `include_str!`, the delimiter parser, the `ReplCommand`
enum row + allowlist, the primer topic-name cross-reference). The **delimiter
format is the contract between us** — agree it before Phase 5 so the parser and
the content match. (If `/dev` prefers the asset live under `src/agent/` or a
`resources/` dir, that is fine — `/docs` only needs a stable path to author
into and an agreed delimiter.)

## 6. Couplings to reconcile

- **`/repl` (command UX, `repl/spec.md §17`):** owns the `/syntax` and bare-
  `/syntax`-index *experience* — exact output framing, the topic-list rendering,
  unknown-topic behaviour ("no such topic; available: …"), and any **alias map**
  (`lambda`→`fn`, `struct`→`deftype`). This plan supplies the per-topic gloss
  text (the index lines) and the block format; `/repl` decides how they render
  and the not-found UX.
- **`/dev (src/)` (wiring + asset location):** owns the `include_str!`, the
  delimiter parser, the `ReplCommand` row + read-only allowlist entry, and the
  **primer topic-name cross-reference** (the compact in-primer list of available
  topic names so the agent knows the vocabulary to pull). The **delimiter format
  + asset path** are the shared contract — confirm before Phase 5.
- **`/spec` (Phase-5 validation gate):** validates each topic's forms and
  cross-links against the current spec (projection accuracy, no normative
  change). Also receives the primer-vs-spec `match`-shape finding (§4) for
  disposition.
- **`/qa` (defect repro):** if a Phase-5 example that *should* compile does not,
  `/qa` authors the narrow failing repro before Pillar 1 closes.

## 7. Phase-5 deliverables (forward note, not this phase)

1. `src/syntax/cheatsheet.txt` (content only) — ~24 topic blocks per §3 format,
   every example verified-compiling per §4.
2. The per-topic gloss lines handed to `/repl` for the bare-`/syntax` index.
3. The topic-name list handed to `/dev` for the primer cross-reference.
4. `/spec` sign-off on projection accuracy; `/docs` sign-off on
   verified-compiling; both before close.
