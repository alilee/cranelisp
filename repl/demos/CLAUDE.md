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

The top-level `showcase` script builds the binary and delegates to `demo-player.py` for live PTY-based playback:

```bash
./repl/showcase ring0          # build + play Ring 0 demo
./repl/showcase ring1          # build + play Ring 1 demo
./repl/showcase --list         # list available demos
```

### Live PTY playback — no filtering

The showcase delegates to `demo-player.py` which runs the REPL in a real PTY. Each line is typed character-by-character into the live REPL process, and the REPL's actual output appears in real time. There is no capture-then-replay step — the viewer sees exactly what the REPL produces, when it produces it.

This approach supports:
- **Interactive IO** (`read-line` works because the REPL has a real terminal)
- **Shell escapes** (`; #!` output appears inline where it occurs)
- **Session restart** (`/quit` trampoline: the REPL exits, a new one starts in the same run dir, and the demo continues — `; Restored user.cl` appears naturally)
- **File watching** (timing is real — the REPL sees files when they're created)

If the showcase output looks wrong, the fix goes in the REPL — not in the showcase or the player.

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
| `ring2a.demo` | 2A | Prelude discovery, trait-dispatched operators, float dispatch, docstrings, deftrait/impl, constrained polymorphism |
| `ring2b.demo` | 2B | Display trait, string equality, user-defined types + Display impl, constrained polymorphism across traits |
| `ring3.demo` | 3 | Macros & metaprogramming: defmacro with docstrings, multi-clause macros, prelude macros (case/cond/str), string primitives, threading macros with /expand |
| `exemplar-progress.demo` | 3 | Exemplar: Sudoku domain types (ADTs), grid geometry, 4x4 backtracking solver with formatted output |
| `stdlib-progress.demo` | 3 | Prelude vocabulary: trait-dispatched operators, constrained polymorphism, Option/Result matching, string ops, compose, threading |
| `ring4a.demo` | 4A | IO foundation: Pure, bind, platform stdio, print, IO composition |
| `ring4b.demo` | 4B | IO sequencing: do, bind!, named IO results, IO + conditionals |
| `ring4c.demo` | 4C | REPL hardening: prelude ADT display, type annotations, Option |
| `ring4d.demo` | 4D | Developer tools: /source, /clif, panic recovery (div-by-zero) |
| `ring4e.demo` | 4E | Trace special form, corrected IO display, /mod namespace switching |
| `ring4f.demo` | 4F | Auto-currying: partial application, curried composition, map with curried fn, /run-tests |
| `ring4g.demo` | 4G | Module caching (--no-cache), curried trait operators (+ 5), map with curried ops, non-Var rejection error, /run-tests |
| `ring4h.demo` | 4H | Session persistence (user.cl), shell escape (;#!), shell-driven module creation, file watching, --link standalone executable, /run-tests |
| `ring4i.demo` | 4I | Higher-kinded types (Functor/fmap), lazy sequences (range-from/iterate/take), terminal styling narrative, checked division panic + recovery, /run-tests |
| `ring4j.demo` | 4J | Lenient evaluation (parallel independent let bindings, cost heuristic), auto IO scheduling (commutative bind! chains), trait methods as first-class values (§7.6), /run-tests |
| `v4a.demo` | — | Pipeline v4 skeleton — --v4 delegates to old pipeline, identical results |
| `v4b.demo` | — | Pipeline v4 scheduler — primitive-only programs compile through scheduler-driven path |

Each sprint, `/repl` extends this library.

## Prelude and Trait Availability

With prelude loading (Sprint 11+), the REPL loads `stdlib/prelude.cl` at startup, which provides the four core traits (`Num`, `Eq`, `Ord`, `Display`) and their primitive type implementations, plus standard macros and convenience functions. **Operators like `+`, `-`, `*`, `/` work from the first prompt** — demos no longer need inline trait boilerplate.

Decision 17 (eliminating bespoke compiler-seeded trait registration) was resolved in Sprint 9: core traits now flow through the normal `register_trait_decl` / `register_trait_impl` pipeline in `builtins.rs`. The prelude loading mechanism (Sprint 11) then made these traits available via stdlib rather than requiring inline setup in demos.

**Current state**: Demos can freely use operators, trait-dispatched functions, and prelude macros without any setup. The `first-session.demo` script uses bare `+` and `/imports` — these work because the prelude provides `Num` and its `Int`/`Float` implementations at startup.

**If prelude loading is broken**: If a sprint breaks prelude loading (e.g., import registration ordering), operators will fail with unresolved trait errors. The fix belongs in the compiler pipeline (`/int`), not in the demos. Do not add inline trait boilerplate to demos as a workaround — file a FIXME against `/int` or `/qa` instead.

## Conventions

- Keep demos short (20–40 lines of input) — they should be watchable in 2–3 minutes
- Build a narrative: introduce a concept, show it, combine with previous concepts
- **Use REPL discoverability to introduce new features.** When a demo uses a feature for the first time, let the viewer discover it through the REPL — type the name, see its type/description, then use it. For example, ring2a introduces `+` which comes from the prelude: run `/imports` to see what's available, type `+` to see it's `Num.+`, type `Num` to see the trait. The REPL's self-documenting output sets up each section, not the demo author's comments. Comments are section breaks at most.
- End with something satisfying — a composition of features that feels powerful
- Each ring's demo should be self-contained (doesn't depend on previous demos)
