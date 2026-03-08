# REPL Demo Scripts

Owned by `/repl`. A growing library of demo scripts that showcase the REPL experience at each ring.

## Purpose

Demo scripts are the REPL's "portfolio" — short, narrated sessions that show off what the language can do interactively. They grow with each sprint: `/repl` adds, extends, or refines scripts as new features land.

## Format: `.demo` files

Demo scripts use a format that is almost valid Cranelisp:

```
; Comment lines (semicolons) — displayed as section headers
; Blank lines — pause between sections

(+ 1 2)

; Bare expressions are REPL input — typed character-by-character
(defn double [x] (mul-i64 x 2))
(double 21)

; REPL slash commands are valid input (but not valid .cl)
/help
```

### Rules

- Every line is sent to the REPL — comments, blanks, expressions, slash commands
- The showcase types each line at the `> ` prompt, then shows whatever the REPL produced
- No line gets special treatment — if the REPL silently re-prompts for a comment, that's what the viewer sees
- Files use `.demo` extension
- One demo per ring, plus optional themed demos (e.g., `adt-tour.demo`)

### What makes it almost `.cl`

- `;` is the Cranelisp comment character
- Expressions are bare (no prefix)
- Only `/commands` and line-orientation prevent it from being a valid batch program

## Running Demos

The top-level `showcase` script builds the binary and pipes the demo straight into the REPL:

```bash
./repl/showcase ring0          # build + play Ring 0 demo
./repl/showcase ring1          # build + play Ring 1 demo
./repl/showcase --list         # list available demos
```

### Transparent pipe — no filtering

The showcase sends the **entire** `.demo` file to the REPL as stdin, captures the raw output, then replays it with typing effects. It MUST NOT filter, reorder, or suppress any REPL behavior. If comments produce errors, definitions show `<closure>`, or types are unqualified — that is what the viewer sees. The showcase shows the product as-is.

1. **Phase 1** — Send the entire `.demo` file to the REPL process. Capture raw stdout.
2. **Phase 2** — Parse output by splitting on `"> "` prompts to pair each input line with its result. Replay with typing effects: comments displayed dimmed, expressions typed character-by-character with the REPL's actual result shown instantly.

If the showcase output looks wrong, the fix goes in the REPL — not in the showcase.

### Run isolation

Each playback creates a timestamped directory under `repl/demos/runs/`:
```
runs/2026-03-05T14-30-00_ring1/
```

The REPL process `chdir`s into this directory, so `.cache` artifacts and any other side effects are isolated per run. The `runs/` directory is git-ignored.

### Timing parameters (environment variables)

| Variable | Default | Description |
|----------|---------|-------------|
| `DEMO_TYPING_MS` | `30` | Milliseconds between characters |
| `DEMO_LINE_PAUSE_MS` | `1500` | Milliseconds pause before each input line |
| `DEMO_COMMENT_PAUSE_MS` | `800` | Milliseconds after comment display |
| `DEMO_FAST` | unset | If set, all delays are zero (CI mode) |

## Script Library

| File | Ring | Description |
|------|------|-------------|
| `first-session.demo` | 0–3 | Learner progression: evaluate, define, inspect, mistakes, recover |
| `ring0.demo` | 0 | Arithmetic, booleans, let, if, defn, recursion, TCO |
| `ring1.demo` | 1 | Strings, ADTs, pattern matching, closures, higher-order, Vecs |
| `ring2a.demo` | 2A | Trait-dispatched operators, float dispatch, deftrait, constrained polymorphism, default methods |
| `ring2b.demo` | 2B | String equality, Display trait, user-defined impls, constrained polymorphism |
| `ring3.demo` | 3 | Macros: defmacro, quasiquote, multi-clause, splice, prelude macros, /expand |
<!-- FIXME(/repl): Add exemplar-progress.demo and stdlib-progress.demo to this table. exemplar-progress.demo: Ring 3, "Exemplar progress: Sudoku domain ADTs, backtracking solver, Display trait, grid display". stdlib-progress.demo: check its content and add appropriate description. -->

Each sprint, `/repl` extends this library:
- **Ring 4**: IO, platforms, full REPL experience (slash commands, trace, run-tests)

## Prelude and Trait Availability

With prelude loading (Sprint 11+), the REPL loads `stdlib/prelude.cl` at startup, which provides the four core traits (`Num`, `Eq`, `Ord`, `Display`) and their primitive type implementations, plus standard macros and convenience functions. **Operators like `+`, `-`, `*`, `/` work from the first prompt** — demos no longer need inline trait boilerplate.

Decision 17 (eliminating bespoke compiler-seeded trait registration) was resolved in Sprint 9: core traits now flow through the normal `register_trait_decl` / `register_trait_impl` pipeline in `builtins.rs`. The prelude loading mechanism (Sprint 11) then made these traits available via stdlib rather than requiring inline setup in demos.

**Current state**: Demos can freely use operators, trait-dispatched functions, and prelude macros without any setup. The `first-session.demo` script uses bare `+` and `/sig +` — these work because the prelude provides `Num` and its `Int`/`Float` implementations at startup.

**If prelude loading is broken**: If a sprint breaks prelude loading (e.g., import registration ordering), operators will fail with unresolved trait errors. The fix belongs in the compiler pipeline (`/int`), not in the demos. Do not add inline trait boilerplate to demos as a workaround — file a FIXME against `/int` or `/qa` instead.

## Conventions

- Keep demos short (20–40 lines of input) — they should be watchable in 2–3 minutes
- Build a narrative: introduce a concept, show it, combine with previous concepts
- Use comments to set up each section — the viewer should understand what's coming
- End with something satisfying — a composition of features that feels powerful
- Each ring's demo should be self-contained (doesn't depend on previous demos)
