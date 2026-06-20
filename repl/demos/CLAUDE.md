# REPL Demo Scripts

Owned by `/repl`. A curated set of demos that showcase **the language**, played
live through the REPL.

## Purpose

Demos demonstrate Cranelisp's capabilities, organized by language feature, not by
sprint or development milestone. Each demo takes one capability and shows it
working interactively, building toward the Sudoku solver as the centerpiece. A
viewer who watches the active set in order gets a guided introduction to the
language — values and types, ADTs, functions, traits, modules, effects — and then
sees them combine to solve a real problem.

This is the durable framing: **demonstrate the language, not the changelog.** When
a new capability lands, fold it into the demo for the relevant capability (a new
collection verb → `values-and-types` or `modules`; a new trait feature → `traits`).
Do not add a sprint-named demo to the active set.

## The active set

Eight capability-named demos, each self-contained, each replaying green against
the prebuilt binary. They consume the **curated surface** (see below) — the same
idiomatic surface the exemplar uses.

| File | Demonstrates |
|------|--------------|
| `tour.demo` | A five-minute tour: the read-eval loop, literals + types, operators, defn, type errors caught, recursion, `show`/`str`. |
| `values-and-types.demo` | Inference; trait operators across Int/Float; `show`/`str`; Vecs; import-on-demand collection verbs; one polymorphic definition over many types. |
| `adts-and-matching.demo` | `deftype` enums and field-carrying variants; `match`; `Option`/`Result`; recursive types; the Sudoku `Cell` in miniature. |
| `functions.demo` | `defn`/`fn`; closures; higher-order functions; `compose`; threading (`->`/`->>`); accumulator recursion. |
| `traits.demo` | Operators as trait methods; inferred trait bounds; `deftrait`/`impl`; constrained polymorphism over a user trait. |
| `modules.demo` | `/imports`; import-on-demand; fully-qualified origins; unbound-name discoverability; how the exemplar's modules fit together. |
| `io-and-effects.demo` | `(IO a)` values; `platform stdio`/`print`; `do`/`bind!` sequencing; `Pure`/`bind`; effects in control flow; the exemplar's main shape. |
| `sudoku.demo` | The centerpiece: ADT domain types, grid geometry, a backtracking solver, formatted output, and a single `print` effect — a 4×4 sibling of `exemplar/user.cl`. |

The arc deliberately ends at `sudoku.demo`, which reuses every concept the prior
demos introduced.

## The archive (regression guards)

`archive/` holds the historical sprint/ring-named demos (`ring*`, `v4*`, `s81`).
They are **kept, not retired** — they exercise the language end-to-end and catch
real regressions, so they must still replay green from their archive path. They
are NOT part of the guided showcase narrative (they narrate development history,
which the active set deliberately omits). When the binary changes, the archive is
a regression sweep; the active set is the portfolio.

Do not add new demos to `archive/`. Do not delete archived demos to "clean up" —
they are the durable regression net.

## Curated surface

Demos consume the post-de-leak curated surface (S86). Run them with:

```bash
CRANELISP_LIB=$PWD/stdlib CRANELISP_PLATFORM_PATH=$PWD/target/debug
```

- **Bare via the prelude**: operators `+ - * / = != < > <= >=`; `show`, `str`;
  types `Int Bool Float String Option Some None Result Ok Err List Nil Cons`;
  macros `vec list when unless cond case -> ->> def def- const const- do bind! pure`.
- **Import-on-demand** (NOT bare): `count`/`get`/`assoc` from `collections.vec`,
  `first`/`rest` from `collections.list`. Import by name, then use unqualified.
- **Avoid `conj` for Vecs of heap ADTs** (carried defect DEF-2 — refcount bug in
  the wrapper). Use `assoc`/`vec-push` for ADT-element Vecs; `conj` only for
  scalar Vecs. The Sudoku demo uses Int Vecs with `assoc`/`get`/`count`, which are
  unaffected.
- Demos model the idiomatic surface the exemplar uses: operators bare, `=` for
  strings, collection verbs imported.

## Format: `.demo` files

Almost-valid Cranelisp, line-oriented:

```
; Comment lines (semicolons) — displayed as dimmed section headers
; Blank lines — a visual pause

(+ 1 2)

; Bare expressions are REPL input — typed character-by-character
(defn double [x] (* x 2))
(double 21)

; Slash commands are valid REPL input (but not valid .cl)
/help
```

### Rules

- Every line is sent to the REPL — comments, blanks, expressions, slash commands.
- The player types each line at the `> ` prompt, then shows whatever the REPL
  produced. No line gets special treatment.
- Files use the `.demo` extension.

### What makes it almost `.cl`

- `;` is the Cranelisp comment character.
- Expressions are bare (no prefix).
- Only `/commands` and line-orientation prevent it from being a valid batch
  program.

## Running demos

The top-level `showcase` script builds the binary and delegates to
`demo-player.py` for live PTY playback:

```bash
./repl/showcase sudoku          # build + play the Sudoku demo (active)
./repl/showcase ring4s          # build + play an archived guard (falls through to archive/)
./repl/showcase --list          # list the active set + the archived guards
```

`showcase` resolves a name as `demos/<name>.demo` first, then falls back to
`demos/archive/<name>.demo`. `--list` presents the active set and an "Archived
(regression guards)" section. `demo-player.py` replays any path directly:

```bash
DEMO_FAST=1 CRANELISP_LIB=$PWD/stdlib CRANELISP_PLATFORM_PATH=$PWD/target/debug \
  python3 repl/demos/demo-player.py repl/demos/sudoku.demo $PWD/target/debug/cranelisp
```

### Live PTY playback — no filtering

The player runs the REPL in a real PTY. Each line is typed character-by-character
into the live process, and the REPL's actual output appears in real time. There is
no capture-then-replay step — the viewer sees exactly what the REPL produces.

This supports interactive IO (`read-line`), shell escapes (`; #!`), session
restart (the `/quit` trampoline), and real file-watching timing.

If the showcase output looks wrong, the fix goes in the REPL — not in the showcase
or the player.

### Run isolation

Each playback creates a timestamped directory under `repl/demos/runs/`. The REPL
`chdir`s into it, so `.cache` artifacts are isolated per run. `runs/` is
git-ignored.

### Timing parameters (environment variables)

| Variable | Default | Description |
|----------|---------|-------------|
| `DEMO_TYPING_MS` | `30` | Milliseconds between characters |
| `DEMO_LINE_PAUSE_MS` | `1500` | Milliseconds pause before each input line |
| `DEMO_COMMENT_PAUSE_MS` | `800` | Milliseconds after comment display |
| `DEMO_FAST` | unset | If set, all delays are zero (CI / verification mode) |

## Conventions

- **Demonstrate the language, not the changelog.** Organize by capability. No
  sprint/ring/phase narration in the active set. Comments are section headers and
  brief framing, not development history.
- Keep each demo watchable in 2–3 minutes (~20–40 lines of input).
- **Let the REPL do the talking.** When a demo introduces a name, type it bare and
  let the REPL's self-documenting output describe it (its type, origin, docstring)
  before using it. `/sig`, `/imports`, `/info`, and a bare name at the prompt set
  up each section. The self-documenting REPL is itself a feature on display.
- **Build toward Sudoku.** Where a capability maps onto the solver, point at it
  (the `Cell` ADT, the accumulator-recursion board formatter, the main effect
  shape). `sudoku.demo` then pays off the whole arc.
- Each demo is self-contained — it does not depend on a prior demo's session.
- End with something that combines the concepts and feels complete.
- Consume the curated surface (above). Don't reach for raw `*-i64`/`str-eq`/`vec-*`
  primitives where a curated operator or imported verb exists.

## If the prelude breaks

The REPL loads `stdlib/prelude.cl` at startup, providing the core traits, the
common types, the operators, and the standard macros. If a change breaks prelude
loading, operators fail with unresolved-trait errors. The fix belongs in the
compiler pipeline (`/int` / `/qa`), not in the demos — file a FIXME, do not add
inline trait boilerplate as a workaround.
