---
number: 0335
target: /docs
filed_by: /arch
filed_at: 2026-06-13
sprint_filed: 81
refers_to: user/ (currently empty), src/main.rs (parse_args / resolve_target), design/arch/bounded-contexts.md §6 "Per-surface documentation", design/arch/fixmes/0298
status: open
---

# CLI reference doc owed under `user/` — the int outside-in CLI contract has no single home

## Issue

The S81 W-Retire pass (FIXME 0298, /arch) retired `facades/int.md` — int is a
binary, so the library-facade pattern never fit it. The reframe (user-ratified
2026-06-08) classified int's actual boundaries: the **CLI surface** (the three
modes `--run` / `--link` / REPL + options `--no-color`, worker counts, target,
parsed in `src/main.rs::parse_args` / `resolve_target`) is int's real outside-in
contract, but it has **no single user-facing reference** — the modes + options are
scattered across `spec/`, and `user/` is currently empty.

The retirement records the CLI's canonical home as the `src/main.rs` crate-level
`//!` rustdoc narrative (int-owned, the compiler-side record) plus a user-facing
CLI reference under `user/` (`/docs`-owned). BC §6 "Per-surface documentation"
names the `user/` doc as owed. The `//!` narrative is `/dev`-on-int's to author
(tracked separately under the int wave); THIS FIXME is the `/docs`-owned half.

## Proposed resolution

`/docs` authors a CLI reference under `user/` covering:

- The three modes — `--run <file.cl>`, `--link <file.cl>`, REPL (no mode flag) —
  what each does, what artefact each produces.
- Options: `--no-color`, worker-count flags, the entry-target argument +
  `resolve_target` precedence (per `repl/spec.md §0.5` / `src/CLAUDE.md`
  "entry-file precedence" — a `<name>.cl` file IS the entry; a `<name>/`
  directory is the project root).
- Cross-links: REPL experience → `repl/spec.md`; language behaviour → `spec/`.

The authoritative behaviour is `src/main.rs::parse_args`'s `Action` /
`SessionSettings` / `CliError` shapes — read those for the option set rather than
restating from memory.

## Context

The 8th and final facade retirement (the int facade) completes the arc — no live
facade-spec documents remain. The one outside-in contract that lacked a home is
the CLI, and `user/` is the natural place for it (it is `/docs`-owned and
currently empty). Not blocking any compiler work; this is documentation
completeness so a newcomer can learn the CLI from one place.
