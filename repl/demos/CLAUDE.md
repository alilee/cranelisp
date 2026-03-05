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

- `;` lines are comments — displayed dimmed as section headers, not sent to the REPL
- Blank lines are pauses — the player waits briefly
- All other lines are REPL input — typed slowly, then the REPL response is shown
- No special prefix on input lines — they look like real REPL input
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

The showcase uses a two-phase approach:

1. **Phase 1** — Parse the `.demo` file. Send only expression lines to the REPL as piped stdin (comments and blanks are filtered out). Capture stdout.
2. **Phase 2** — Replay the demo: comments displayed dimmed as section headers, expression input typed character-by-character with the REPL result shown instantly after each.

This avoids the known REPL issue where comment-only lines produce `error: parse error at 0..0: empty input` (the reader strips `;` but the REPL evaluates the empty result). The REPL should eventually skip empty input — filed for the `src/repl.rs` owner — but the showcase works around it.

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
| `first-session.demo` | 0–1 | Learner progression: evaluate, define, inspect, mistakes, recover |
| `ring0.demo` | 0 | Arithmetic, booleans, let, if, defn, recursion, TCO |
| `ring1.demo` | 1 | Strings, ADTs, pattern matching, closures, higher-order, Vecs |

Each sprint, `/repl` extends this library:
- **Ring 2**: Traits, modules, constrained polymorphism
- **Ring 3**: Macros, derive, standard library
- **Ring 4**: IO, platforms, full REPL experience (slash commands, trace, run-tests)

## Conventions

- Keep demos short (20–40 lines of input) — they should be watchable in 2–3 minutes
- Build a narrative: introduce a concept, show it, combine with previous concepts
- Use comments to set up each section — the viewer should understand what's coming
- End with something satisfying — a composition of features that feels powerful
- Each ring's demo should be self-contained (doesn't depend on previous demos)
