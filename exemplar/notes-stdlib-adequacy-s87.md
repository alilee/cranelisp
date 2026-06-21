# Exemplar-driven stdlib-adequacy review — S87 Stage C.1

Owner: `/port`. Status: **Phase 5 — full collated/prioritized gap list COMPLETE.**
This supersedes the Phase-3 C1–C10 recon (preserved below §"First
reconnaissance" for traceability). The collated intake for `/stdlib` lives in
`stdlib/plan-stdlib.md §26.4` (authored by `/stdlib`, not here — this file is
`/port`'s working notes + the hand-off list).

---

## §FULL — Collated, prioritized gap list (Phase 5, complete pass)

Pass scope: every site in `grid.cl`, `solver.cl`, `html.cl`, `form.cl`,
`user.cl` (idiom-bearing bodies; test helpers surveyed only for repeated
hand-rolled patterns). Each row classified [STDLIB]/[COMPILER], authoring vs
adoption, cross-checked against the current stdlib surface
(`collections/vec.cl`, `num/int.cl`, `text/string.cl`, `seq/lazy.cl`) and
against `spec/11-stdlib.md §11.4a` (the 0402 reserved-name rule).

### Routing summary (read this first)

- **[COMPILER] → Stage-B backlog** (NOT in-sprint /stdlib): G1 (bitwise
  intrinsics — FIXME **0416** filed `target: /arch`), G2 (DEF-2 `conj`
  heap-ADT RC — repro already queued for /qa; no new FIXME per
  `feedback_no_fixme_with_failing_test`).
- **[STDLIB] authoring → /stdlib §26.4 intake** (verb does NOT exist; pure-
  composable): G3 `range`, G4 `char->digit` (+ `digit->char`), G5 `str-assoc`/
  `replace-at`.
- **[STDLIB] adoption → /stdlib §26.4 note + exemplar refresh** (verb EXISTS;
  exemplar hand-rolls): G6 `int-to-string` (digit-string), G7 `num.int/rem`,
  G8 `repeat-str` (make-dots), G9 `str` macro (deliberate avoidance — flag, do
  not force), G10 reuse `rem`/`row-of`/`col-of` in user.cl.

### Reserved-name cross-check (§11.4a / FIXME 0402)

None of the proposed authoring verbs collide with the reserved bare names
(`map`/`filter`/`reduce`/`count`/`get`/`conj`/`assoc`/`first`/`rest`):

- `range`, `char->digit`, `digit->char`, `str-assoc`/`replace-at` are NOT on the
  reserved list → free to curate AND (if desired) bare-promote.
- **Caveat for `range`:** it is the natural producer feeding the future
  collection trait's `map`/`filter`/`reduce`. Curating `range` is fine; just do
  not let it pull a bare `map`/`reduce` into the prelude (§11.4a). `range`
  itself is unreserved.
- All `[STDLIB] adoption` targets (`int-to-string`, `rem`, `repeat-str`, `str`)
  already exist at their qualified paths and are §11.4a-clean.

### Collated table

| # | site (file:line) | awkward thing | proposed verb / fix | class | authoring vs adoption | priority |
|---|---|---|---|---|---|---|
| G1 | `grid.cl:83-126` (`pow2`,`bit-set?`,`bit-clear`,`bit-set`,`bit-count-helper`,`bit-count`,`bit-lowest-helper`,`bit-lowest`) | whole 9-bit mask layer simulates `<< >> & ~` + popcount in `+ - * / pow2` (~55 lines) | bitwise intrinsics `bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount` + `num/bits.cl` wrappers | **[COMPILER]** | authoring (language/runtime gap — not stdlib-composable) | **HIGHEST contortion**, but gated on /spec+/backend → Stage-B (FIXME 0416) |
| G2 | `grid.cl:161-169,184-202,350-388`; `solver.cl:331-338`; `html.cl:224-253` | every heap-ADT (`Cell`) accumulator uses bare `vec-push`, NOT curated `conj`, because `conj` corrupts heap-ADT element RC in a loop | fix wrapper-RC defect, then swap `vec-push`→`conj` | **[COMPILER] / DEF-2** | adoption-blocked-by-defect (`conj` exists, corrupts) | important; repro queued for /qa → /backend (no new FIXME) |
| G3 | `solver.cl:222-270` (4 board-format helpers); `solver.cl:99-118` grids-differ; `grid.cl:109-126,161-169` bit/peer scans; `html.cl:74-131` form/solution rows; `form.cl:33-38` make-dots; `solver.cl:319-326` count-determined | pervasive **manual index-recursion** `(if (= i N) acc (helper (+ i 1) (combine acc …)))` — the "for i in 0..N, fold into acc" shape, hand-threaded ~15 times | eager **`range :Int :Int -> (Vec Int)`** (composable from `seq/lazy.cl range-from` + `seq-take`, or a direct loop) → then `(vec-reduce f init (range 0 9))` / `(vec-map f (range 0 81))` | **[STDLIB]** | **authoring** (no eager `range`; only lazy `range-from` exists, uncurated for this) | **HIGHEST stdlib leverage** — cleans ~15 sites |
| G4 | `form.cl:41-53` (`parse-digit-char`, 11-arm `cond`); `grid.cl:191-202` (`make-grid-helper`, 10-arm nested `if`) | char→int via N-way `if`/`cond` ladder, twice (~22 lines total) | **`char->digit :String -> :Int`** (returns -1 sentinel for non-digit; composable from `char-at`/comparison or an `index-of` over "0123456789"). Pair with **`digit->char`** for G6's inverse. | **[STDLIB]** | **authoring** (verb does not exist) | high — two clean ladder collapses |
| G5 | `form.cl:57-59` (`set-char-at`) | functional string-index-set via `(str-concat (substring s 0 idx) (str-concat ch (substring s (+ idx 1) len)))` | **`str-assoc`/`replace-at :String :Int :String -> :String`** (composable from `substring`/`str-concat`) | **[STDLIB]** | **authoring** (verb does not exist) | medium — one site, but a common idiom; cheap |
| G6 | `solver.cl:197-207` (`digit-string`, 10-arm nested `if`) | int 1-9 → its digit string via 10-arm `if` | `(if (= v 0) "." (int-to-string v))` — **`int-to-string` is a primitive** | **[STDLIB]** | **adoption** (verb exists; hand-rolled lookup) | medium — trivial, removes 11 lines |
| G7 | `grid.cl:68-69` (`rem-i64` def); used `grid.cl:92,134,353,377`; `user.cl:47` inline `(- idx (* (/ idx 9) 9))` | `rem-i64` redefined inline; **`num/int.cl` already exports `rem`** with identical semantics | import `num.int/rem` (or keep `rem-i64` as a documented domain alias — Design Decision currently justifies inline) | **[STDLIB]** | **adoption** (verb exists; exemplar redefines) | low-medium — DEF currently rationalises this; flag, don't force |
| G8 | `form.cl:33-38` (`make-dots`/`make-dots-helper`) | 81 dots built by recursive `str-concat` | `(repeat-str "." 81)` — **`text.string/repeat-str` exists** | **[STDLIB]** | **adoption** (verb exists; hand-rolled) | medium — clean one-liner |
| G9 | `html.cl:24-47` (`css`), `html.cl:92-166` (all `*-page`), `solver.cl:286-289` build-output, `user.cl:48,59,74-78,87-90` | 4-6-level nested `str-concat` pyramids glue string literals | `str` macro (`(str a b c d …)`) flattens them — **`text.string/str` exists** | **[STDLIB]** | **adoption** (macro exists; author deliberately avoids per CLAUDE.md "no show-dispatch overhead in production") | **nice-to-have / optional** — deliberate choice; flag, DO NOT force |
| G10 | `user.cl:45-48` (`field-name`) | `col` = inline `rem` (G7) AND `row`/`col` from idx duplicate `grid/row-of`,`grid/col-of` | reuse `num.int/rem` + export/import `grid/row-of`,`grid/col-of` | **[STDLIB]** | **adoption** (verbs exist; exemplar duplicates) | low — single site |

### Counts

- **[COMPILER] gaps: 2** — G1 (bitwise intrinsics, FIXME 0416), G2 (DEF-2 conj RC, repro queued).
- **[STDLIB] authoring gaps: 3** — G3 `range`, G4 `char->digit`(+`digit->char`), G5 `str-assoc`/`replace-at`.
- **[STDLIB] adoption gaps: 5** — G6 `int-to-string`, G7 `num.int/rem`, G8 `repeat-str`, G9 `str` macro (optional), G10 reuse rem/row-of/col-of.
- **Total: 10 gaps** (2 compiler, 8 stdlib).

### Highest-leverage

1. **G3 `range`** — single highest stdlib win: collapses ~15 hand-threaded
   index-recursion helpers across all four pure modules. Cheap to author
   (compose over existing `range-from`/`seq-take`, or a direct accumulator
   loop), §11.4a-clean.
2. **G1 bitwise intrinsics** — biggest raw contortion (~55 lines), but COMPILER:
   gated on /spec+/backend, routed via FIXME 0416 to Stage-B.
3. **G4 `char->digit`** + **G5 `str-assoc`** — two clean authoring wins, ~25
   lines combined, both §11.4a-clean.

### Hand-off to /stdlib (for `plan-stdlib.md §26.4` intake)

**Cheap + obvious authoring candidates (do these first):**

- **G4 `char->digit :String -> :Int`** (-1 sentinel) in `text/string.cl` — and
  its inverse **`digit->char :Int -> :String`** (which also serves G6). Both are
  small index-of/lookup helpers over the digit chars.
- **G5 `str-assoc`/`replace-at :String :Int :String -> :String`** in
  `text/string.cl` — three-line `substring`+`str-concat` splice.

**Slightly larger (but highest-value) authoring candidate:**

- **G3 eager `range :Int :Int -> (Vec Int)`** — decide home (`collections/vec.cl`
  or a new `num`/`seq` eager helper) and inclusive/exclusive convention. NOTE
  §11.4a caveat: `range` is unreserved, but it feeds `map`/`reduce`; do not let
  it bare-promote those. Composable from `seq.lazy/range-from`+`seq-take` or a
  direct loop.

**Adoption notes (exemplar-refresh candidates, low stdlib effort):**

- G6 swap `digit-string` → `(if (= v 0) "." (int-to-string v))` (or
  `digit->char`).
- G8 swap `make-dots` → `(repeat-str "." 81)`.
- G7/G10 reuse `num.int/rem` + `grid/row-of`/`col-of` (currently rationalised by
  a Design Decision — confirm whether to retire the inline `rem-i64` alias).
- **G9 `str` macro — DO NOT force.** `exemplar/CLAUDE.md` documents the nested
  `str-concat` as a deliberate "no show-dispatch overhead in production" choice.
  List it as available, not as a required cleanup.

> NOTE: the exemplar `.cl` refresh (applying the adoption swaps once G3/G4/G5
> land) is a *later* /port pass, NOT this read-only review and NOT /stdlib's
> intake. /stdlib authors the verbs; /port adopts them afterward.

---

## Review lens (the question)

> Where is the exemplar code awkward to express because the stdlib lacks an
> obvious feature?

A "site" qualifies when the author, reading the four pure modules + `user.cl`,
did one of:

1. **wrote an inline workaround** for something a curated verb should do,
2. **reached for a raw primitive** (`vec-push`, `char-at`, `str-concat`, manual
   index loops) where a curated Clojure-style verb exists or should exist,
3. **hand-rolled a combinator / collection op** (map/filter/reduce/range/repeat)
   that the stdlib already provides or could provide,
4. **contorted the data flow** (e.g. character-by-character string scans, manual
   accumulator threading) because an obvious higher-order op is missing.

## Method (Phase 5/6 execution plan)

1. Read each module end-to-end in load order: `grid` → `solver` → `html` →
   `form` → `user`. (`tests.cl` is a runner, not idiom-bearing; test bodies are
   surveyed only for repeated hand-rolled patterns.)
2. For every qualifying site record: `file:line` · what was awkward · the
   one-line idiomatic rewrite · the stdlib verb that enables it.
3. **Classify each (the load-bearing distinction):**
   - **[STDLIB]** Pure stdlib gap — a fn/macro composable from existing
     primitives. Candidate for Stage C.2 in-sprint `/stdlib` authoring.
   - **[COMPILER]** Compiler/language gap — needs typecheck/codegen/spec
     support. Feeds the Stage B audit backlog / FIXME store. NOT in-sprint
     stdlib work.
4. Cross-check each [STDLIB] candidate against the *current* stdlib surface
   (`collections/vec.cl`, `seq.cl`, `num/int.cl`, `text/string.cl`) — many
   verbs already EXIST and the gap is really "exemplar hand-rolls instead of
   importing." Those are **adoption gaps**, not authoring gaps: distinguish
   "verb missing" from "verb exists, unused."
5. Prioritize: blocking > important > nice-to-have, weighted by site count
   (a verb that would clean up 10 sites beats one that cleans 1).
6. Hand the collated list to `/stdlib` for `plan-stdlib.md` intake; route
   [COMPILER] entries to the Stage B backlog.

## Output format (one row per gap)

| site (file:line) | awkward thing | proposed verb / fix | class | already in stdlib? |

## Important framing note — DEF-2 distorts the read

The exemplar deliberately uses the **bare `vec-push` primitive** instead of the
curated `conj` everywhere it accumulates a Vec of heap ADTs, because of the
carried **DEF-2** wrapper-RC defect (`conj` corrupts heap-ADT elements in a
loop; see `CLAUDE.md` Known Issues). So almost every `vec-push` site below is
NOT a stdlib *authoring* gap — `conj` exists — it is a **compiler defect
masquerading as a stdlib adoption gap**. These route to [COMPILER] / the DEF-2
repro, not to C.2. The adequacy review must not double-count them as "missing
verb."

---

## First reconnaissance — candidate awkward sites (SUPERSEDED by §FULL above; kept for traceability)

> The C1–C10 recon below is the Phase-3 first pass. It is now subsumed by the
> §FULL collated table (G1–G10). Mapping: C3→G1, C7(conj half)→G2, C5/C7(range
> half)→G3, C2→G4, C8→G5, C1→G6, C4→G7, C6→G8, C9→G9, C10→G10.


Honest assessment: the four modules are already **fairly clean** post the S86
idiom pass (trait operators bare, `count`/`get`/`assoc` curated). The remaining
awkwardness clusters in three areas: (a) **no bitwise primitives** → arithmetic
simulation of bit ops; (b) **string-as-char-array** manual scans where a
higher-order string op would read better; (c) **manual index-recursion loops**
where `range`/`vec-map`/`reduce` over an index sequence would be idiomatic. Plus
the DEF-2 `vec-push` cluster (compiler, not stdlib).

### C1 — `digit-string`: 9-way nested `if` int→string  ·  [STDLIB]
`solver.cl:197-207`. A 9-arm nested `if` mapping int 1-9 to its string digit.
`int-to-string` exists as a primitive and would collapse the whole thing to one
call (`(if (= v 0) "." (int-to-string v))`). **Adoption gap** — the verb
exists; the author hand-rolled a lookup. Trivial cleanup.

### C2 — `parse-digit-char` / `make-grid-helper`: char→int via N-way `if`  ·  [STDLIB]
`form.cl:41-53` (10-arm `cond`) and `grid.cl:191-202` (10-arm nested `if`
building Given cells). Both hand-roll "is this char a digit, and which one."
Proposed: a stdlib `char-to-digit :String -> :Int` (returns -1 / sentinel for
non-digits) in `text/string.cl`, composable from `char-at`/comparison. Would
collapse two ~10-line ladders. **Authoring gap** (verb does not exist today).

### C3 — bitmask ops simulate bitwise via `/ * - pow2`  ·  [COMPILER]
`grid.cl:83-126` (`pow2`, `bit-set?`, `bit-clear`, `bit-set`, `bit-count`,
`bit-lowest`). The whole bitmask layer reimplements `<<`, `>>`, `&`, popcount
in arithmetic because **Cranelisp has no `bit-and`/`bit-or`/`bit-shift`
primitives** (documented Design Decision). This is a genuine **language/runtime
gap**, not stdlib-composable (you cannot write efficient `bit-and` from `+ - *
/`). Routes to the Stage B backlog / a FIXME for `/spec`+`/backend` (bitwise
intrinsics). Largest single source of "contorted to fit" code in the exemplar.

### C4 — `rem-i64` redefined inline  ·  [STDLIB adoption]
`grid.cl:68-69` defines `rem-i64` as `(- a (* (/ a b) b))`. **`num/int.cl`
already exports `rem`** with that exact semantics. Pure adoption gap: import
`num.int/rem` instead of the inline helper. (`col-of`/`box-of` use it too.)

### C5 — `format-row*` / `format-board*`: manual index-recursion accumulators  ·  [STDLIB]
`solver.cl:222-270` (four mutually-tail-recursive helpers threading `(row col
acc)` to build the board string). The pattern is "for i in 0..9, concat into
acc" — i.e. a `reduce` over a numeric range. A stdlib **`range :Int :Int ->
(Vec Int)`** + the existing `vec-reduce` (or a `str-join`/`map`+`join`) would
replace ~50 lines of bespoke loops with a few combinator calls. **Authoring
gap**: `range` does not exist; `vec-reduce`/`vec-map` DO. (Same shape recurs in
`html.cl` form-row/solution-row helpers and `form.cl` make-dots.)

### C6 — `make-dots`: hand-rolled string repeat  ·  [STDLIB adoption]
`form.cl:33-38`. Builds 81 dots by recursive `str-concat`. **`text/string.cl`
already exports `repeat-str`** — `(repeat-str "." 81)` is the one-liner. Pure
adoption gap.

### C7 — `peers-helper` accumulates with bare `vec-push`  ·  [COMPILER / DEF-2]
`grid.cl:161-169`. Builds the 20-element peer list via `vec-push` rather than
`conj`, AND the whole "filter 0..81 by a predicate into a Vec" is a
`(vec-filter pred (range 0 81))` shape. Two findings: the `vec-push` is the
**DEF-2 carve-out** (compiler, not stdlib — `conj` exists but corrupts), and the
filter-over-range is a [STDLIB] `range` adoption (see C5). Documents the DEF-2
distortion concretely.

### C8 — `set-char-at`: functional string-index-set via substring splice  ·  [STDLIB]
`form.cl:57-59`. `(str-concat (substring s 0 idx) (str-concat ch (substring s
(+ idx 1) len)))`. A common enough op to warrant a curated
`str-assoc`/`replace-at :String :Int :String -> :String`. **Authoring gap**;
composable from existing `substring`/`str-concat`, so it is pure-stdlib.

### C9 — `css` / `*-page`: deeply nested `str-concat` pyramids  ·  [STDLIB]
`html.cl:24-47` (css) and every `*-page` fn. 4-6 levels of nested `str-concat`
to glue string literals. The `str` macro (`text/string.cl:18`) takes `&args`
and concatenates — `(str a b c d)` would flatten these pyramids dramatically.
**Adoption gap** — `str` macro exists; the author avoided it (CLAUDE.md cites
"no `str`-macro/`show`-dispatch overhead in production" — a deliberate choice,
so flag as *optional/ergonomic*, severity nice-to-have, not blocking).

### C10 — `field-name` recomputes `idx/9` and inlines `rem`  ·  [STDLIB adoption]
`user.cl:45-48`. `col` computed as `(- idx (* (/ idx 9) 9))` — an inline `rem`
(see C4) — and `row`/`col` from idx duplicates `grid/row-of`,`grid/col-of`.
Adoption: reuse `num.int/rem` and/or export `row-of`/`col-of` from grid.

### Honest "already clean" notes
- The `match` + ADT usage (`eliminate`, `solve`, `propagate`) is idiomatic and
  needs no stdlib help.
- `count`/`get`/`assoc` are used well throughout (the S86 idiom pass landed).
- `Option`/`SolveResult` threading reads cleanly; no `fn/option` combinator gap
  jumped out (though `solve`'s `match … [None … (Some g) …]` chains in
  `eliminate-from-peers-helper` could *optionally* use an `option/and-then`).

---

## Provisional classification tally (recon only — not the final list)

- **[STDLIB] authoring gaps** (verb missing, pure-composable → C.2 candidates):
  C2 `char-to-digit`, C5/C7 `range`, C8 `str-assoc`/`replace-at`.
- **[STDLIB] adoption gaps** (verb EXISTS, exemplar hand-rolls → cheap idiom
  swap, may inform C.2 + an exemplar refresh): C1 `int-to-string`, C4
  `num.int/rem`, C6 `repeat-str`, C9 `str` macro, C10 reuse rem/row-of.
- **[COMPILER] gaps** (→ Stage B backlog / FIXME, NOT C.2): C3 bitwise
  intrinsics (language), C7 DEF-2 `conj` heap-ADT RC (compiler defect; repro
  already queued for `/qa`).

## Priority signal for the full pass
1. **C3 bitwise intrinsics** — biggest contortion, but COMPILER, so it gates on
   `/spec`+`/backend`, not C.2.
2. **C5/C7 `range`** — highest stdlib leverage (cleans board formatting, peers,
   make-dots, html rows — many sites).
3. **C2 `char-to-digit`** + **C8 `str-assoc`** — two clean authoring wins.
4. **C1/C4/C6/C9/C10 adoption swaps** — cheap, but note C9 is a *deliberate*
   avoidance (flag, don't force).
